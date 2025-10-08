#!/bin/bash
# Wrapper script to manage the BFS-Prover tactic server

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PYTHON="$SCRIPT_DIR/.venv/bin/python3"
SERVER="$SCRIPT_DIR/tactic_server.py"
PID_FILE="$SCRIPT_DIR/.tactic_server.pid"
LOG_FILE="$SCRIPT_DIR/.tactic_server.log"

start_server() {
    if [ -f "$PID_FILE" ]; then
        PID=$(cat "$PID_FILE")
        if kill -0 "$PID" 2>/dev/null; then
            echo "Server already running (PID: $PID)"
            return 1
        else
            echo "Removing stale PID file"
            rm -f "$PID_FILE"
        fi
    fi

    echo "Starting BFS-Prover tactic server..."
    echo "(This will take 10-20 seconds to load the model)"

    # Start server in background
    nohup "$PYTHON" "$SERVER" > "$LOG_FILE" 2>&1 &

    # Wait for server to be ready
    sleep 2

    if [ -f "$PID_FILE" ]; then
        PID=$(cat "$PID_FILE")
        echo "✓ Server started (PID: $PID)"
        echo "  Logs: $LOG_FILE"
        echo "  Query with: $PYTHON tactic_query.py --state \"...\""
        return 0
    else
        echo "✗ Server failed to start. Check logs: $LOG_FILE"
        return 1
    fi
}

stop_server() {
    if [ ! -f "$PID_FILE" ]; then
        echo "Server not running (no PID file)"
        return 1
    fi

    PID=$(cat "$PID_FILE")

    if kill -0 "$PID" 2>/dev/null; then
        echo "Stopping server (PID: $PID)..."
        kill "$PID"

        # Wait for shutdown
        for i in {1..10}; do
            if ! kill -0 "$PID" 2>/dev/null; then
                echo "✓ Server stopped"
                rm -f "$PID_FILE"
                return 0
            fi
            sleep 0.5
        done

        # Force kill if still running
        echo "Force killing server..."
        kill -9 "$PID" 2>/dev/null
        rm -f "$PID_FILE"
        return 0
    else
        echo "Server not running (stale PID file)"
        rm -f "$PID_FILE"
        return 1
    fi
}

status_server() {
    if [ -f "$PID_FILE" ]; then
        PID=$(cat "$PID_FILE")
        if kill -0 "$PID" 2>/dev/null; then
            echo "Server running (PID: $PID)"
            echo "Query with: $PYTHON tactic_query.py --state \"...\""
            return 0
        else
            echo "Server not running (stale PID file)"
            return 1
        fi
    else
        echo "Server not running"
        return 1
    fi
}

case "$1" in
    start)
        start_server
        ;;
    stop)
        stop_server
        ;;
    restart)
        stop_server
        sleep 1
        start_server
        ;;
    status)
        status_server
        ;;
    logs)
        if [ -f "$LOG_FILE" ]; then
            tail -f "$LOG_FILE"
        else
            echo "No log file found"
            exit 1
        fi
        ;;
    *)
        echo "Usage: $0 {start|stop|restart|status|logs}"
        exit 1
        ;;
esac
