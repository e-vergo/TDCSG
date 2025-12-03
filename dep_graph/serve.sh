#!/bin/bash
cd "$(dirname "$0")"

# Kill any existing processes on port 8000
echo "Checking for existing servers on port 8000..."
lsof -ti:8000 | xargs kill -9 2>/dev/null
if [ $? -eq 0 ]; then
  echo "Killed existing server(s)"
  sleep 1
else
  echo "No existing servers found"
fi

echo "Starting local server at http://localhost:8000"
echo "Open: http://localhost:8000/index.html"
echo "Press Ctrl+C to stop"
python3 -m http.server 8000
