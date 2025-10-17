# Agent Directive Update: Diagnostic Collection

## Add This Section After "TOOL ACCESS"

Insert the following section immediately after the "TOOL ACCESS" section in the agent directive:

---

### **BUILD & TEST PROTOCOL (CRITICAL)**

**MANDATORY TOOL**: Use `/check_lean.sh` for ALL build verification.

#### The Critical Testing Pattern

After EVERY code change, test using the **errors-only mode**:

```bash
./check_lean.sh --errors-only TDCSG/YourFile.lean
```

**This is your iteration loop:**
1. Make proof attempt
2. Run `./check_lean.sh --errors-only TDCSG/YourFile.lean`
3. Interpret result:
   - `✓ No errors` = SUCCESS, proof works!
   - Any error output = FAILURE, fix and retry

#### Why This Matters

**Token Efficiency**: 99% reduction compared to raw `lake build` output
- More iterations per context window
- Faster proof development
- No context waste on build noise

**Complete Diagnostics**: NEVER uses `head` or `tail`
- See EVERY error with full context
- No clipped messages
- No missed diagnostics

#### Two Modes Available

**1. Errors-Only (Your Default Choice)**
```bash
./check_lean.sh --errors-only TDCSG/YourFile.lean
```
Use when: Testing if proof compiles (99% of the time)

**2. All Diagnostics**
```bash
./check_lean.sh TDCSG/YourFile.lean
```
Use when: Need to see warnings for code quality

#### What You Get

**Success case:**
```
✓ TDCSG/YourFile.lean: No errors
```

**Failure case (complete multi-line error):**
```
error: TDCSG/YourFile.lean:170:2: Type mismatch
  42
has type
  ℕ
of sort `Type` but is expected to have type
  Measurable f.toFun
of sort `Prop`
```

#### Critical Rules

1. **NEVER use `lake build | head` or `lake build | tail`**
   - These clip diagnostics and cause missed errors
   - Use `./check_lean.sh` instead

2. **Test after EVERY change**
   - One modification → one test
   - No batch testing without verification

3. **Trust the output**
   - Tool shows ALL diagnostics for your file
   - Nothing is clipped or hidden
   - Zero diagnostics from other files

4. **Use errors-only for iteration**
   - Warnings don't prevent proof from working
   - Focus on errors during development
   - Check warnings at the end

#### Integration with Workflow

**MANDATORY CYCLE: CHANGE → TEST → CHECK → ITERATE**

```
Step 1: Make proof attempt
  ↓
Step 2: ./check_lean.sh --errors-only TDCSG/YourFile.lean
  ↓
Step 3: If errors → fix → return to Step 2
        If no errors → proof works! → move to next sorry
```

**Example Session:**

```bash
# Attempt 1: Try `ring` tactic
./check_lean.sh --errors-only TDCSG/Examples.lean
# Output: error about missing CommRing instance
# → Learn: Need stronger algebraic structure

# Attempt 2: Add instance hypothesis
./check_lean.sh --errors-only TDCSG/Examples.lean
# Output: error about changed theorem signature
# → Learn: Can't add hypothesis, need different approach

# Attempt 3: Use existing lemma from Mathlib
./check_lean.sh --errors-only TDCSG/Examples.lean
# Output: ✓ No errors
# → SUCCESS! Proof complete, move to next sorry
```

#### Why This Is Mission-Critical

**Before this tool**: Agents clipped diagnostics with `head`/`tail`, missed errors, wasted context on build noise

**With this tool**: Agents see complete diagnostics, 99% token reduction, maximum iterations per context window

**This tool enables your workflow to be efficient and reliable.**

Use it. Use it heavily. Use it after every single code change.

---

## Replace Existing References

**Find and remove** any directive text mentioning:
- `lake build | head`
- `lake build | tail`
- Manual output truncation
- "Check diagnostics carefully for clipping"

**Replace with**: Reference to `./check_lean.sh --errors-only`

---

## Update Summary Statistics Section

If the directive has a "Best Practices" or "Tool Usage" section, add:

**Critical Tool: check_lean.sh**
- 99% token reduction in error checking
- Zero clipped diagnostics
- Mandatory for all build verification
- Use `--errors-only` for iteration loop

---

## Implementation Checklist

When updating agent directive:

- [ ] Add BUILD & TEST PROTOCOL section after TOOL ACCESS
- [ ] Remove references to `lake build | head/tail`
- [ ] Update examples to use `./check_lean.sh`
- [ ] Emphasize `--errors-only` as default testing mode
- [ ] Include token efficiency statistics
- [ ] Note location of full documentation (`/CHECK_LEAN_TOOL.md`)

---

**Critical**: This tool is the difference between agents that waste context on build noise and agents that maximize iterations with clean diagnostics. Make it prominent in the directive.
