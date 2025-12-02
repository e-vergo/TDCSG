#!/usr/bin/env python3
"""Delete dead code declarations - this is complex due to interdependencies."""
import sys
print("Dead code deletion requires careful manual review due to:")
print("1. Cascade dependencies (dead code calling other dead code)")
print("2. Large multi-line proofs with complex structure")
print("3. Risk of breaking builds")
print("")
print("Recommend: Manual deletion file-by-file, testing after each file")
print("See docs/dead_code_by_file.md for prioritized list")
sys.exit(1)
