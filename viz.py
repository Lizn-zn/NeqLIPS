import sys
import webbrowser
from pathlib import Path
import http.server
import socketserver
import threading
import os

# Constants should be in UPPERCASE
PORT = 8001
MAX_PORT_ATTEMPTS = 100
HANDLER = http.server.SimpleHTTPRequestHandler
HTML_PATH = "LIPS/Visualization/ptree.html"

def start_server():
    global PORT
    attempts = 0
    
    while attempts < MAX_PORT_ATTEMPTS:
        try:
            with socketserver.TCPServer(("", PORT), HANDLER) as httpd:
                print(f"Serving at port {PORT}")
                httpd.serve_forever()
        except OSError:
            print(f"Port {PORT} is in use")
    
def main(json_file_path):
    # Validate JSON file path
    json_path = Path(json_file_path)
    if not json_path.exists():
        print(f"Error: JSON file '{json_file_path}' does not exist.")
        return 1
    
    if not json_path.suffix.lower() == '.json':
        print(f"Warning: File '{json_file_path}' might not be a JSON file.")
    
    # Convert to relative path from HTML file location
    try:
        relative_json_path = os.path.relpath(json_path.absolute(), start=HTML_PATH)
    except ValueError as e:
        print(f"Error creating relative path: {e}")
        return 1
    
    # Start server in background thread
    server_thread = threading.Thread(target=start_server, daemon=True)
    server_thread.start()
    
    # Construct and open URL
    url = f"http://localhost:{PORT}/{HTML_PATH}?json={relative_json_path}"
    print(f"Opening URL: {url}")
    webbrowser.open(url)
    
    # Keep main thread running until interrupted
    try:
        server_thread.join()
    except KeyboardInterrupt:
        print("\nServer stopped.")
        return 0

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python viz.py <path_to_json_file>")
        sys.exit(1)
    
    sys.exit(main(sys.argv[1]))
