from flask import Flask, request, jsonify, render_template, session, redirect, url_for
from flask_session import Session
import os
import sqlite3
import base64
from datetime import datetime
import cv2
import face_recognition
import numpy as np
from werkzeug.utils import secure_filename
from io import BytesIO
from PIL import Image
import random
import smtplib
import json
import time
import hashlib

# ---------------- APP CONFIG ---------------- #
app = Flask(__name__)
UPLOAD_FOLDER = 'static/uploads'

# use absolute path for DB to avoid multiple DB files in different working directories
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATABASE = os.path.join(BASE_DIR, 'Election.db')

app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER

CANDIDATE_UPLOAD_FOLDER = os.path.join(app.config['UPLOAD_FOLDER'], 'candidates')
if not os.path.exists(CANDIDATE_UPLOAD_FOLDER):
    os.makedirs(CANDIDATE_UPLOAD_FOLDER)

if not os.path.exists(UPLOAD_FOLDER):
    os.makedirs(UPLOAD_FOLDER)

app.config['SECRET_KEY'] = 'your_secret_key'
app.config['SESSION_TYPE'] = 'filesystem'
Session(app)

# ---------------- DATABASE ---------------- #
def init_db():
    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS Voter_details (
            Name TEXT,
            Email TEXT,
            Username TEXT UNIQUE,
            Password TEXT,
            Photo TEXT
        )
    ''')
    conn.commit()
    conn.close()

def init_candidate_table():
    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS Candidate (
            Name TEXT,
            Party TEXT,
            Photo TEXT,
            Description TEXT
        )
    ''')
    conn.commit()
    conn.close()

def init_vote_table():
    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS Vote (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            Name TEXT NOT NULL,
            Username TEXT UNIQUE NOT NULL,
            Email TEXT NOT NULL,
            Candidate TEXT NOT NULL,
            Timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    conn.commit()
    conn.close()

def init_result():
    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS Result (
            Name TEXT,
            Photo TEXT,
            Party TEXT,
            Votes INTEGER
        )
    ''')
    conn.commit()
    conn.close()

# Blockchain table for persistence
def init_blockchain_table():
    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS Blockchain (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            block_index INTEGER,
            votes TEXT,
            timestamp REAL,
            previous_hash TEXT,
            hash TEXT,
            nonce INTEGER
        )
    ''')
    conn.commit()
    conn.close()

# # Ensure DB tables exist no matter how Flask is started
# @app.before_first_request
# def initialize_database():
#     init_db()
#     init_candidate_table()
#     init_vote_table()
#     init_result()
#     init_blockchain_table()

# ---------------- Simple Blockchain ---------------- #
class Block:
    def __init__(self, index, votes, timestamp, previous_hash, nonce=0, hash_value=None):
        self.index = index
        self.votes = votes  # list of vote dicts
        self.timestamp = timestamp
        self.previous_hash = previous_hash
        self.nonce = nonce
        # if hash_value provided (loading from DB) use it, else compute
        self.hash = hash_value if hash_value is not None else self.compute_hash()

    def compute_hash(self):
        # create a deterministic dict excluding 'hash' to compute hash
        block_dict = {
            'index': self.index,
            'votes': self.votes,
            'timestamp': self.timestamp,
            'previous_hash': self.previous_hash,
            'nonce': self.nonce
        }
        block_string = json.dumps(block_dict, sort_keys=True)
        return hashlib.sha256(block_string.encode()).hexdigest()

    def to_dict(self):
        return {
            'index': self.index,
            'votes': self.votes,
            'timestamp': self.timestamp,
            'previous_hash': self.previous_hash,
            'nonce': self.nonce,
            'hash': self.hash
        }

class Blockchain:
    def __init__(self):
        self.chain = []  # list of Block
        self.pending_votes = []
        init_blockchain_table()
        self.load_chain_from_db()
        if not self.chain:
            # create genesis
            genesis = Block(0, [], time.time(), "0")
            self.chain.append(genesis)
            self.save_block_to_db(genesis)

    def load_chain_from_db(self):
        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()
        # select columns matching table schema
        cursor.execute("SELECT block_index, votes, timestamp, previous_hash, hash, nonce FROM Blockchain ORDER BY block_index ASC")
        rows = cursor.fetchall()
        conn.close()
        if not rows:
            return
        self.chain = []
        for block_index, votes_json, timestamp, previous_hash, hash_value, nonce in rows:
            try:
                votes = json.loads(votes_json) if votes_json else []
            except Exception:
                votes = []
            # use nonce and hash_value as provided
            block = Block(block_index, votes, timestamp, previous_hash, nonce, hash_value)
            self.chain.append(block)

    def save_block_to_db(self, block: Block):
        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()
        cursor.execute('''
            INSERT INTO Blockchain (block_index, votes, timestamp, previous_hash, hash, nonce)
            VALUES (?, ?, ?, ?, ?, ?)
        ''', (block.index, json.dumps(block.votes), block.timestamp, block.previous_hash, block.hash, block.nonce))
        conn.commit()
        conn.close()

    def add_vote(self, voter_id, candidate_id, constituency_id=None):
        # constituency_id optional for compatibility; store timestamp
        vote = {
            'voter_id': voter_id,
            'candidate_id': candidate_id,
            'constituency_id': constituency_id,
            'timestamp': time.time()
        }
        self.pending_votes.append(vote)
        return vote

    def mine_pending_votes(self):
        if not self.pending_votes:
            return None
        block = Block(len(self.chain), self.pending_votes.copy(), time.time(), self.chain[-1].hash)
        # simple: no POW, set nonce=0, compute hash already done in Block
        self.chain.append(block)
        self.save_block_to_db(block)
        self.pending_votes = []
        return block

    def is_chain_valid(self):
        # verify linking and hashes
        for i in range(1, len(self.chain)):
            curr = self.chain[i]
            prev = self.chain[i-1]
            if curr.previous_hash != prev.hash:
                return False, f"Broken link at index {i}"
            # recompute hash
            if curr.compute_hash() != curr.hash:
                return False, f"Hash mismatch at index {i}"
        return True, "Chain valid"

    def has_voted(self, voter_id):
        # Check across all blocks' votes
        for block in self.chain:
            for v in block.votes:
                if v.get('voter_id') == voter_id:
                    return True
        # also check pending votes
        for v in self.pending_votes:
            if v.get('voter_id') == voter_id:
                return True
        return False

# instantiate blockchain
voting_blockchain = Blockchain()

# ---------------- UTILS ---------------- #
def generate_otp():
    return str(random.randint(0,0))

def send_email(receiver_email, otp):
    sender_email = "bharatiyavotingsystemdemo@gmail.com"
    sender_password = "rbhb zdof ehkx fzui"
    try:
        server = smtplib.SMTP("smtp.gmail.com", 587)
        server.starttls()
        server.login(sender_email, sender_password)
        message = f"Subject: OTP Verification\n\nYour OTP is {otp}"
        server.sendmail(sender_email, receiver_email, message)
        server.quit()
        return True
    except Exception as e:
        print("Error sending email:", e)
        return False

# ---------------- ROUTES ---------------- #
@app.route('/')
def home():
    return render_template("index.html")

@app.route('/admin')
def admin():
    return render_template("Admin.html")

@app.route('/Voter_login')
def Voter_login():
    return render_template("Voter_login.html")

@app.route('/Voter_registration')
def Voter_registration():
    return render_template("Voter_registration.html")

@app.route('/register', methods=['POST'])
def register():
    try:
        full_name = request.form['fullName']
        email = request.form['email']
        username = request.form['username']
        password = request.form['password']
        photo_data_url = request.form['photoData']

        if "base64," in photo_data_url:
            _, encoded = photo_data_url.split(",", 1)
        else:
            return jsonify({"success": False, "message": "Invalid photo data."})

        # Decode photo and get face encoding
        image_data = base64.b64decode(encoded)
        img = Image.open(BytesIO(image_data)).convert('RGB')
        img_np = np.array(img)
        new_face_encodings = face_recognition.face_encodings(img_np)

        if not new_face_encodings:
            return jsonify({"success": False, "message": "No face detected in the photo."})
        new_encoding = new_face_encodings[0]

        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()

        # Check if email already exists
        cursor.execute("SELECT 1 FROM Voter_details WHERE Email=?", (email,))
        if cursor.fetchone():
            conn.close()
            return jsonify({"success": False, "message": "Email already exists."})

        # Check if face already exists
        cursor.execute("SELECT Photo FROM Voter_details")
        existing_photos = cursor.fetchall()
        for (photo_path,) in existing_photos:
            if os.path.exists(photo_path):
                known_image = face_recognition.load_image_file(photo_path)
                known_encodings = face_recognition.face_encodings(known_image)
                if known_encodings:
                    match = face_recognition.compare_faces([known_encodings[0]], new_encoding, tolerance=0.45)
                    if match[0]:
                        conn.close()
                        return jsonify({"success": False, "message": "Face already exists in the system."})

        # Save new photo
        photo_filename = f"{username}.png"
        photo_path = os.path.join(app.config['UPLOAD_FOLDER'], photo_filename).replace("\\", "/")
        with open(photo_path, "wb") as f:
            f.write(image_data)

        # Insert voter
        cursor.execute('''
            INSERT INTO Voter_details (Name, Email, Username, Password, Photo)
            VALUES (?, ?, ?, ?, ?)
        ''', (full_name, email, username, password, photo_path))
        conn.commit()
        conn.close()

        return jsonify({"success": True})

    except sqlite3.IntegrityError:
        return jsonify({"success": False, "message": "Username already exists."})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)})



# ---------------- FACE LOGIN ---------------- #
@app.route('/face-login', methods=['POST'])
def face_login():
    if 'photo' not in request.files:
        return jsonify({'status': 'error', 'message': 'No image uploaded'}), 400

    file = request.files['photo']

    try:
        img = Image.open(BytesIO(file.read())).convert('RGB')
        img_np = np.array(img)
        unknown_face_encodings = face_recognition.face_encodings(img_np)
        if not unknown_face_encodings:
            return jsonify({'status': 'error', 'message': 'No face detected.'})
        unknown_encoding = unknown_face_encodings[0]
    except Exception as e:
        return jsonify({'status': 'error', 'message': f'Image error: {str(e)}'})

    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute("SELECT Name, Email, Username, Photo FROM Voter_details")
    Voters = cursor.fetchall()
    conn.close()

    for Voter in Voters:
        name, email, username, photo_path = Voter
        known_image_path = os.path.join(UPLOAD_FOLDER, os.path.basename(photo_path))
        if os.path.exists(known_image_path):
            known_image = face_recognition.load_image_file(known_image_path)
            known_encodings = face_recognition.face_encodings(known_image)
            if not known_encodings:
                continue
            result = face_recognition.compare_faces([known_encodings[0]], unknown_encoding, tolerance=0.45)
            if result[0]:
                session['user'] = {'name': name, 'email': email, 'username': username, 'photo': f'/{photo_path}'}
                otp = generate_otp()
                session['otp'] = otp
                session['otp_email'] = email
                send_email(email, otp)
                return jsonify({'status': 'success', 'data': session['user'], 'message': 'Face recognized. OTP sent.'})

    return jsonify({'status': 'error', 'message': 'Face not recognized.'})

@app.route('/login', methods=['POST'])
def login():
    try:
        data = request.get_json()
        username = data.get('username')
        password = data.get('password')
        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()
        cursor.execute('''
            SELECT Name, Email, Photo FROM Voter_details
            WHERE Username=? AND Password=?
        ''', (username, password))
        result = cursor.fetchone()
        conn.close()
        if result:
            name, email, photo_path = result
            session['user'] = {'name': name, 'email': email, 'username': username, 'photo': photo_path}
            return jsonify({'success': True, 'data': session['user']})
        else:
            return jsonify({'success': False, 'message': 'Profile not found.'})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)})

@app.route("/verify-otp", methods=["POST"])
def verify_otp():
    data = request.get_json()
    email = data.get("email")
    entered_otp = data.get("otp")
    if not entered_otp or not email:
        return jsonify({"success": False, "message": "Email or OTP missing"})
    if session.get("otp") == entered_otp and session.get("otp_email") == email:
        session.pop("otp")
        session.pop("otp_email")
        return jsonify({"success": True})
    return jsonify({"success": False, "message": "Invalid OTP"})

@app.route('/admin-login', methods=['POST'])
def admin_login():
    try:
        data = request.get_json()
        username = data.get('username')
        password = data.get('password')
        if username == os.getenv('ADMIN_USERNAME') and password == os.getenv('ADMIN_PASSWORD'):
            return jsonify({'success': True})
        return jsonify({'success': False, 'message': 'Invalid credentials.'})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)})

# ---------------- CANDIDATES & VOTES ---------------- #
@app.route('/add-candidate', methods=['POST'])
def add_candidate():
    try:
        init_candidate_table()
        init_vote_table()
        init_result()
        name = request.form['name']
        party = request.form['party']
        description = request.form['description']
        photo = request.files['photo']
        if not photo:
            return jsonify({'success': False, 'message': 'Photo required.'})
        filename = secure_filename(f"{name}.png")
        photo_path = os.path.join(CANDIDATE_UPLOAD_FOLDER, filename).replace("\\", "/")
        photo.save(photo_path)
        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()
        cursor.execute('INSERT INTO Candidate (Name, Party, Photo, Description) VALUES (?, ?, ?, ?)',
                       (name, party, photo_path, description))
        conn.commit()
        conn.close()
        return jsonify({'success': True})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)})

@app.route('/candidates')
def candidates():
    if 'user' not in session:
        return jsonify({'error': 'User not logged in'}), 403
    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute("SELECT Name, Party, Photo, Description FROM Candidate")
    candidates = cursor.fetchall()
    conn.close()
    user = session['user']
    return render_template('candidates.html', candidates=candidates, user=user)

@app.route('/submit-vote', methods=['POST'])
def submit_vote():
    if 'user' not in session:
        return jsonify({'success': False, 'message': 'User not logged in'}), 403
    try:
        data = request.get_json()
        candidate = data.get('candidate')
        constituency = data.get('constituency')  # optional
        if not candidate:
            return jsonify({'success': False, 'message': 'Candidate not specified'}), 400
        user = session['user']
        username = user['username']

        # Double vote prevention: check Vote table
        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()
        cursor.execute("SELECT * FROM Vote WHERE Username=?", (username,))
        if cursor.fetchone():
            conn.close()
            return jsonify({'success': False, 'message': 'Already voted!'}), 409

        # Also check blockchain (in case someone bypassed DB)
        if voting_blockchain.has_voted(username):
            # optionally insert into DB if missing, but safe to return error
            conn.close()
            return jsonify({'success': False, 'message': 'Already voted (blockchain record).'}), 409

        # Add to blockchain pending votes and mine immediately
        voting_blockchain.add_vote(username, candidate, constituency)
        mined_block = voting_blockchain.mine_pending_votes()

        # Save to Vote DB for compatibility / UI
        cursor.execute('INSERT INTO Vote (Name, Username, Email, Candidate) VALUES (?, ?, ?, ?)',
                       (user['name'], username, user['email'], candidate))
        conn.commit()
        conn.close()

        # Convert mined_block to dict safely (may be None)
        block_dict = mined_block.to_dict() if mined_block else None

        return jsonify({'success': True, 'message': 'Vote submitted successfully!', 'block': block_dict})
    except Exception as e:
        return jsonify({'success': False, 'message': f'Error: {str(e)}'})

@app.route('/get-voters', methods=['GET'])
def get_voters():
    try:
        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()

        # Get all voters
        cursor.execute("SELECT Name, Username, Email FROM Voter_details")
        voters = cursor.fetchall()

        # Get all votes
        cursor.execute("SELECT Username FROM Vote")
        voted_usernames = {row[0] for row in cursor.fetchall()}

        voter_list = []
        for name, username, email in voters:
            voter_list.append({
                'name': name,
                'username': username,
                'email': email,
                'voted': username in voted_usernames
            })

        conn.close()
        return jsonify(voter_list)
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/get-stats', methods=['GET'])
def get_stats():
    try:
        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()
        cursor.execute("SELECT Name, Photo, Party FROM Candidate")
        candidates = cursor.fetchall()
        stats = []
        for name, photo, party in candidates:
            cursor.execute("SELECT COUNT(*) FROM Vote WHERE Candidate=?", (name,))
            votes = cursor.fetchone()[0]
            stats.append({'name': name, 'photo': photo, 'party': party, 'votes': votes})
        conn.close()
        return jsonify(stats)
    except Exception as e:
        return jsonify({'error': str(e)})

@app.route('/save-results', methods=['POST'])
def save_results():
    try:
        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()
        cursor.execute("CREATE TABLE IF NOT EXISTS Result (Name TEXT, Photo TEXT, Party TEXT, Votes INTEGER)")
        cursor.execute("DELETE FROM Result")
        cursor.execute("SELECT Name, Photo, Party FROM Candidate")
        candidates = cursor.fetchall()
        for name, photo, party in candidates:
            cursor.execute("SELECT COUNT(*) FROM Vote WHERE Candidate=?", (name,))
            votes = cursor.fetchone()[0]
            cursor.execute("INSERT INTO Result (Name, Photo, Party, Votes) VALUES (?, ?, ?, ?)",
                           (name, photo, party, votes))
        conn.commit()
        conn.close()
        return jsonify({'success': True})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)})

@app.route('/result', methods=['GET'])
def result():
    try:
        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()
        cursor.execute("SELECT Name, Photo, Party, Votes FROM Result")
        results = cursor.fetchall()
        conn.close()

        if not results:
            return "No results found. Please calculate results first."

        # Format results
        formatted_results = [
            {'name': r[0], 'photo': r[1], 'party_name': r[2], 'votes': r[3]}
            for r in results
        ]

        # Find maximum votes
        max_votes = max(r['votes'] for r in formatted_results)

        # Find all top candidates (possible tie)
        top_candidates = [r for r in formatted_results if r['votes'] == max_votes]

        # Randomly choose one if tie
        if len(top_candidates) > 1:
            winner = random.choice(top_candidates)
        else:
            winner = top_candidates[0]

        # Mark only the chosen winner
        for r in formatted_results:
            r['is_winner'] = (r['name'] == winner['name'])

        # Add current date for display
        election_date = datetime.now().strftime("%B %d, %Y")

        return render_template(
            'result.html',
            results=formatted_results,
            election_date=election_date
        )

    except Exception as e:
        return f"Error: {str(e)}"


@app.route('/check-result-or-vote', methods=['POST'])
def check_result_or_vote():
    if 'user' not in session:
        return jsonify({'message': 'User not logged in.'}), 403
    user = session['user']
    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute("SELECT COUNT(*) FROM Result")
    if cursor.fetchone()[0] > 0:
        conn.close()
        return jsonify({'redirectTo': 'result'})
    cursor.execute("SELECT 1 FROM Vote WHERE Username=? AND Email=?", (user['username'], user['email']))
    has_voted = cursor.fetchone() is not None
    conn.close()
    if has_voted:
        return jsonify({'message': 'Already voted. Wait for results.'})
    return jsonify({'redirectTo': 'candidates'})

@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for("home"))

@app.route('/delete-election', methods=['POST'])
def delete_election():
    try:
        conn = sqlite3.connect(DATABASE)
        cursor = conn.cursor()
        for table in ['Voter_details', 'Candidate', 'Result', 'Vote', 'Blockchain']:
            cursor.execute(f"DROP TABLE IF EXISTS {table}")
        conn.commit()
        conn.close()
        for folder in [UPLOAD_FOLDER, CANDIDATE_UPLOAD_FOLDER]:
            if os.path.exists(folder):
                for file in os.listdir(folder):
                    file_path = os.path.join(folder, file)
                    if os.path.isfile(file_path):
                        os.remove(file_path)
        # reset in-memory blockchain
        voting_blockchain.chain = []
        voting_blockchain.pending_votes = []
        # recreate genesis
        genesis = Block(0, [], time.time(), "0")
        voting_blockchain.chain.append(genesis)
        voting_blockchain.save_block_to_db(genesis)
        return jsonify({'success': True})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)})

# ---------------- Blockchain endpoints ---------------- #
@app.route('/blockchain', methods=['GET'])
def get_blockchain():
    # returns chain as JSON (not too heavy, block size expected small)
    chain_data = [b.to_dict() for b in voting_blockchain.chain]
    return jsonify({'length': len(chain_data), 'chain': chain_data})

@app.route('/verify-chain', methods=['GET'])
def verify_chain():
    valid, message = voting_blockchain.is_chain_valid()
    return jsonify({'valid': valid, 'message': message})

if __name__ == '__main__':
    # keep these as a fallback for python app.py
    init_db()
    init_result()
    init_candidate_table()
    init_vote_table()
    init_blockchain_table()
    app.run(debug=True)
