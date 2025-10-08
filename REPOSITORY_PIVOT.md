# Repository Pivot Summary

**Date**: October 8, 2025
**Decision**: Pivot from TDCSG formalization to BFS-Prover MCP tool development

## Rationale

This repository originally started as an effort to formalize results from the paper "Two-Disk Compound Symmetry Groups" in Lean 4. During that work, we developed a valuable Model Context Protocol (MCP) server for the BFS-Prover model.

**The MCP tool proved to be more valuable than the specific formalization work**, so we decided to pivot the repository to focus entirely on developing and documenting the BFS-Prover MCP server.

## What Was Removed

### TDCSG Formalization (27 files deleted)
- **TDCSG/** directory - All Lean 4 formalization files
  - Analysis/, Core/, Theorems/, Theory/, Tools/ subdirectories
  - 14 Lean source files with mathematical proofs
- **TDCSG.lean** - Main project file
- **CLAUDE.md** - TDCSG-specific AI assistant instructions (35KB)
- **START_HERE.md** - TDCSG onboarding document
- **two-disk_compound_symmetry_groups.tex** - Research paper (36KB)
- **BFS_PROVER_DEBUG_SUMMARY.md** - Old debug notes

### Statistics
- **Files deleted**: 27
- **Lines removed**: 3,725
- **Disk space freed**: ~150KB of source code
- **Remaining sorries**: 27 (no longer relevant)

## What Was Kept

### BFS-Prover MCP Infrastructure (Core Value)
- **bfs_prover_mcp/** - MCP server implementation
  - `server.py` - FastMCP server with tool definitions
  - `model.py` - llama-cpp-python integration (**CPU-mode fix applied**)
  - `prompts.py` - BFS-Prover prompt formatting
  - `__init__.py` - Package initialization

### Documentation (Enhanced)
- **README.md** - **Completely rewritten** for MCP focus
  - Installation instructions
  - Usage examples
  - Architecture overview
  - Troubleshooting guide
- **BFS_PROVER_MCP_GUIDE.md** - Comprehensive usage guide (10KB)
- **BFS_PROVER_FIX_SUMMARY.md** - Technical details of CPU-mode fix (3KB)
- **LICENSE** - MIT license

### Testing & Development
- **tests/** directory (newly organized)
  - `test_bfs_debug.py` - Debug mode testing
  - `test_bfs_prover.py` - Full model testing
  - `test_bfs_simple.py` - Simple generation testing
  - `test_cpu_only.py` - CPU-only mode validation
- **requirements.txt** - Python dependencies (NEW)

### Infrastructure
- **lakefile.lean** - Minimal Lean project configuration
- **lean-toolchain** - Lean 4 version specification
- **bfs_prover_mcp_server.sh** - Server startup script
- **.mcp.json** - MCP configuration
- **.venv/** - Python virtual environment
- **BFS-Prover-V2-32B-GGUF/** - Model storage directory

## Key Technical Achievements

### 1. Fixed llama_decode -3 Error
**Problem**: Model was generating 0 tactics due to Metal backend issues
**Solution**: Changed to CPU-only mode (n_gpu_layers=0)
**Result**: ✅ Model now generates tactics successfully (~6s for 10 suggestions)

### 2. MCP Integration Working
**Status**: ✅ Fully operational
**Tools Available**:
- `mcp__bfs_prover__suggest_tactics` - Generate tactics
- `mcp__bfs_prover__model_info` - Check model status
- `mcp__bfs_prover__reload_model` - Reload model

### 3. Performance Benchmarks
- **Model Load Time**: ~1.5s
- **Generation Time**: ~6s for 10 tactics
- **Success Rate**: 30-40% make meaningful progress
- **Memory Usage**: ~28GB

## Repository Statistics

### Before Pivot
- **Purpose**: TDCSG Lean 4 formalization
- **Primary Content**: Mathematical proofs (14 Lean files)
- **Sorries**: 27 remaining
- **Documentation**: TDCSG-focused (CLAUDE.md, START_HERE.md)
- **MCP**: Supporting tool

### After Pivot
- **Purpose**: BFS-Prover MCP server
- **Primary Content**: MCP server implementation
- **Focus**: AI-powered tactic generation
- **Documentation**: MCP-focused (README.md, guides)
- **Lean**: Minimal setup for testing

## Future Directions

### Near-Term (Next Steps)
1. **Repository Rename**: Consider renaming from "TDCSG" to "bfs-prover-mcp"
2. **PyPI Package**: Package as installable Python module
3. **CI/CD**: Add automated testing with GitHub Actions
4. **Documentation**: Add more examples and use cases

### Medium-Term (Development)
1. **GPU Support**: Fix Metal backend for macOS GPU acceleration
2. **Model Variants**: Support different BFS-Prover model sizes
3. **Caching**: Implement tactic suggestion caching
4. **Benchmarks**: Systematic evaluation on mathlib proofs

### Long-Term (Community)
1. **Open Source Release**: Publish to GitHub as standalone project
2. **Community Contributions**: Accept PRs for improvements
3. **Integration**: Work with other Lean 4 tooling (LSP, etc.)
4. **Documentation**: Video tutorials and blog posts

## Lessons Learned

### What Worked
- ✅ **BFS-Prover Integration**: MCP provides excellent AI tactic generation
- ✅ **CPU-Only Mode**: Reliable and fast enough for practical use
- ✅ **Debug Process**: Systematic troubleshooting led to solution
- ✅ **Documentation**: Comprehensive guides make tool accessible

### What Didn't Work
- ❌ **Metal Backend**: llama_decode -3 errors proved difficult to resolve
- ❌ **TDCSG Progress**: Hit blockers on complex ζ₅ algebra proofs
- ❌ **Time Investment**: Formalization work was slow for the complexity

### Key Insights
1. **Tool > Application**: The MCP tool has broader value than one specific formalization
2. **CPU is Good Enough**: Don't need GPU for this use case
3. **Focus Matters**: Better to do one thing well (MCP server) than split effort
4. **Documentation is Key**: Good docs make the tool usable by others

## Migration Notes

If you cloned this repository before the pivot:

```bash
# Pull the latest changes
git pull origin main

# You'll see the TDCSG files are removed
# The .git history still contains them if needed

# To recover old TDCSG work (if needed):
git checkout <commit-before-pivot> -- TDCSG/

# To view old commits:
git log --all -- TDCSG/
```

## Conclusion

This pivot represents a strategic decision to focus on tool development rather than a specific mathematical formalization. The BFS-Prover MCP server has proven valuable and has broad applicability to Lean 4 proof development.

**The repository is now positioned as a focused, well-documented MCP server project** that can benefit the broader Lean 4 community.

---

For questions or discussion about this pivot, see the commit history or open an issue.
