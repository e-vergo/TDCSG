# BFS-Prover MCP Server

Model Context Protocol (MCP) server exposing BFS-Prover tactic generation as Claude Code tools.

## Overview

This MCP server provides Claude Code with direct access to the BFS-Prover-V2 local LLM for Lean 4 tactic generation. It wraps the existing tactic daemon (port 5678) and exposes it as two MCP tools:

- `mcp__bfs-prover__bfs_suggest_tactics` - Generate tactic suggestions from proof states
- `mcp__bfs-prover__bfs_daemon_status` - Check daemon status

## Architecture

```
Claude Code
    ↓
MCP Server (stdio)
    ↓
Socket Client (client.py)
    ↓
Tactic Daemon (port 5678)
    ↓
BFS-Prover Model (14GB in memory)
```

**Key design decisions:**
- Reuses existing daemon infrastructure (no changes to tactic_server.py)
- Stdio transport for MCP communication
- Comprehensive error handling with actionable suggestions
- Environment-based configuration (host, port, timeout)

## Setup

### Prerequisites

1. **BFS-Prover daemon must be running:**
   ```bash
   ./tactic_server.sh start
   ```

2. **MCP server is configured in `.mcp.json`:**
   ```json
   {
     "mcpServers": {
       "bfs-prover": {
         "type": "stdio",
         "command": ".venv/bin/python",
         "args": ["-m", "bfs_prover_mcp.server"],
         "env": {
           "TACTIC_SERVER_HOST": "localhost",
           "TACTIC_SERVER_PORT": "5678",
           "TACTIC_SERVER_TIMEOUT": "30"
         }
       }
     }
   }
   ```

3. **Restart Claude Code** to load the MCP server

### Verification

Check that the server is available:
```bash
# In Claude Code, the tools should appear with mcp__ prefix:
# - mcp__bfs-prover__bfs_suggest_tactics
# - mcp__bfs-prover__bfs_daemon_status
```

## Tool Reference

### bfs_suggest_tactics

Generate Lean 4 tactic suggestions for a proof state.

**Parameters:**
- `proof_state` (required, string) - Proof state from `lean_goal` tool
- `num_suggestions` (optional, int) - Number of tactics to generate (1-10, default: 5)
- `temperature` (optional, float) - Sampling temperature (0.0-1.0, default: 0.7)
- `max_tokens` (optional, int) - Max tokens per tactic (16-512, default: 128)

**Returns:**
```
Generated 5 tactic suggestions in 2.3s:

1. linarith
2. omega
3. simp_arith
4. constructor
5. have h : n + 1 > 1 := by linarith

💡 Test these with lean_multi_attempt to see which ones work!
```

**Error handling:**
- `daemon_not_running` → Suggests `./tactic_server.sh start`
- `timeout` → Suggests `./tactic_server.sh restart`
- `invalid_input` → Check parameters are in valid ranges
- `unknown_error` → Check logs with `cat .tactic_server.log`

### bfs_daemon_status

Check if the BFS-Prover daemon is running and responsive.

**Parameters:** None

**Returns:**
```
BFS-Prover Daemon Status:
  Status: running
  Port: 5678
  PID: 12345
  Model Loaded: true
```

Or if stopped:
```
BFS-Prover Daemon Status:
  Status: stopped
  Port: 5678
  PID: N/A
  Model Loaded: false

ℹ To start: ./tactic_server.sh start
```

## Usage Examples

### Basic Workflow

**1. Check daemon status first:**
```python
status = mcp__bfs-prover__bfs_daemon_status()
# If stopped, user needs to run: ./tactic_server.sh start
```

**2. Get proof state from Lean file:**
```python
goal = mcp__lean-lsp__lean_goal(
    file_path="/path/to/file.lean",
    line=42,
    column=5
)
```

**3. Generate tactic suggestions:**
```python
result = mcp__bfs-prover__bfs_suggest_tactics(
    proof_state=goal,
    num_suggestions=5,
    temperature=0.7
)
# Returns formatted list of tactics
```

**4. Test all suggestions automatically:**
```python
# Extract tactics from result (they're in numbered list format)
tactics = extract_tactics_from_result(result)

results = mcp__lean-lsp__lean_multi_attempt(
    file_path="/path/to/file.lean",
    line=42,
    snippets=tactics
)
```

**5. Apply the winning tactic:**
```python
# Analyze results, pick best tactic
Edit(
    file_path="/path/to/file.lean",
    old_string="  sorry",
    new_string="  linarith"
)
```

### Complete Sorry Elimination Example

```python
# 1. Check daemon is running
status = mcp__bfs-prover__bfs_daemon_status()
if "stopped" in status:
    # Inform user: "Daemon not running. Run: ./tactic_server.sh start"
    return

# 2. Get proof state
file_path = "/Users/eric/Documents/GitHub/TDCSG/TDCSG/Theory/Pentagon.lean"
goal = mcp__lean-lsp__lean_goal(file_path, line=100, column=3)

# 3. Generate tactics (5-10 suggestions)
result = mcp__bfs-prover__bfs_suggest_tactics(
    proof_state=goal,
    num_suggestions=10,
    temperature=0.7
)

# 4. Extract tactics from result
# Result format: "1. tactic1\n2. tactic2\n..."
lines = result.split('\n')
tactics = []
for line in lines:
    if line and line[0].isdigit():
        # Extract tactic after "N. "
        parts = line.split('. ', 1)
        if len(parts) == 2:
            tactics.append(parts[1])

# 5. Test all tactics
results = mcp__lean-lsp__lean_multi_attempt(
    file_path=file_path,
    line=100,
    snippets=tactics
)

# 6. Analyze results and apply best
# Check diagnostics, goal states, pick tactic that makes progress
# Then Edit() to replace sorry
```

### Adjusting Temperature

**Low temperature (0.3-0.5)** - More deterministic, similar tactics:
```python
result = mcp__bfs-prover__bfs_suggest_tactics(
    proof_state=goal,
    num_suggestions=5,
    temperature=0.3
)
# Good for: Standard algebraic goals, simple arithmetic
```

**Medium temperature (0.6-0.8)** - Balanced diversity:
```python
result = mcp__bfs-prover__bfs_suggest_tactics(
    proof_state=goal,
    num_suggestions=5,
    temperature=0.7
)
# Good for: Most proofs, general use
```

**High temperature (0.9)** - More creative, diverse tactics:
```python
result = mcp__bfs-prover__bfs_suggest_tactics(
    proof_state=goal,
    num_suggestions=10,
    temperature=0.9
)
# Good for: Stuck proofs needing creative approach
```

### Multi-Step Proof Iteration

```python
# Iteratively apply tactics and generate new suggestions

file_path = "TDCSG/Theory/Pentagon.lean"

# Step 1: First sorry
goal_1 = mcp__lean-lsp__lean_goal(file_path, line=100)
result_1 = mcp__bfs-prover__bfs_suggest_tactics(proof_state=goal_1)
# Apply best tactic, replace sorry

# Step 2: After first tactic, new goal appears
goal_2 = mcp__lean-lsp__lean_goal(file_path, line=101)
result_2 = mcp__bfs-prover__bfs_suggest_tactics(proof_state=goal_2)
# Apply next tactic

# Continue until proof complete
```

## Integration with lean-lsp-mcp

The BFS-Prover MCP is designed to work alongside the lean-lsp-mcp server. Typical workflow combines tools from both:

**From lean-lsp-mcp:**
- `lean_goal` - Get proof state
- `lean_multi_attempt` - Test tactics
- `lean_diagnostic_messages` - Check for errors

**From bfs-prover-mcp:**
- `bfs_suggest_tactics` - Generate tactics
- `bfs_daemon_status` - Check readiness

**Complete workflow:**
```
lean_goal → bfs_suggest_tactics → lean_multi_attempt → Edit
```

## Performance

- **First request**: 2-5 seconds (daemon already loaded)
- **Subsequent requests**: 2-5 seconds (consistent)
- **vs. One-shot mode**: 10x faster (daemon avoids 15s model reload)
- **Model size**: ~14GB RAM
- **Success rate**: ~50% compile, ~20% make progress, use as inspiration

## Troubleshooting

### "daemon_not_running" error

```bash
# Start the daemon
./tactic_server.sh start

# Verify it's running
./tactic_server.sh status
```

### "timeout" error

```bash
# Daemon may be overloaded, restart it
./tactic_server.sh restart
```

### MCP server not appearing in Claude Code

1. Check `.mcp.json` configuration is correct
2. Verify `.venv/bin/python` exists and has required packages
3. Restart Claude Code
4. Check Claude Code logs for MCP connection errors

### Tactics don't compile in Lean

This is expected! The model was trained on older mathlib4:
- ~50% of tactics compile without errors
- ~20% make actual progress
- Treat suggestions as inspiration, not gospel
- Lemma names may be outdated but approach is often right

### Slow performance

**Expected:** 2-5s per request in daemon mode

**If slower:**
```bash
# Check daemon is actually running
./tactic_server.sh status

# Restart if needed
./tactic_server.sh restart

# Check logs for issues
./tactic_server.sh logs
```

## Configuration

Environment variables (set in `.mcp.json`):

- `TACTIC_SERVER_HOST` - Daemon host (default: "localhost")
- `TACTIC_SERVER_PORT` - Daemon port (default: "5678")
- `TACTIC_SERVER_TIMEOUT` - Socket timeout in seconds (default: "30")

Example custom configuration:
```json
{
  "env": {
    "TACTIC_SERVER_HOST": "localhost",
    "TACTIC_SERVER_PORT": "5678",
    "TACTIC_SERVER_TIMEOUT": "60"
  }
}
```

## Best Practices

### When to Use BFS-Prover

**⭐ ALWAYS try for:**
- Any sorry where you're stuck for >2 minutes
- Standard algebraic/arithmetic proofs
- Induction proofs over lists/nats
- Existential proofs needing concrete witnesses
- Breaking down complex goals

**Still try, expect mixed results:**
- Custom domain-specific lemmas (adapt suggestions)
- Complex multi-step geometric arguments (use for steps)
- Goals with unusual custom structures

### Maximizing Success Rate

1. **Generate 5-10 suggestions** - Higher chance of success
2. **Use `lean_multi_attempt`** - Test all automatically
3. **Adjust temperature** - Low (0.5) for simple, high (0.9) when stuck
4. **Iterate** - If first batch fails, try different temperature
5. **Extract patterns** - Even failed tactics reveal the right approach
6. **Check for updated lemmas** - Model may suggest outdated names

### Session Workflow

**Start of session:**
```bash
# 1. Start daemon FIRST
./tactic_server.sh start

# 2. Verify it's running
./tactic_server.sh status
```

**During session:**
- Use `bfs_suggest_tactics` liberally (it's fast!)
- Generate 10 suggestions at a time when stuck
- Iterate with different temperatures

**End of session:**
```bash
# Stop daemon to free 14GB RAM
./tactic_server.sh stop
```

## Files

- `server.py` - MCP server (stdio transport, tool definitions)
- `client.py` - Socket client for daemon communication
- `__init__.py` - Package initialization

## See Also

- [TACTIC_SUGGEST_README.md](../TACTIC_SUGGEST_README.md) - Daemon and one-shot mode documentation
- [CLAUDE.md](../CLAUDE.md) - Project guidance including BFS-Prover workflow
- [mcp_spec.txt](../mcp_spec.txt) - MCP server specification

## License

MIT License (see [LICENSE](../LICENSE))
