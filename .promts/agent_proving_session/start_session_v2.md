# **LEAN PROOF COMPLETION: AGENT DIRECTIVE**

**BEGIN IMMEDIATELY. This is not a planning document. Start working NOW.**

---

## **YOUR MISSION**

Eliminate all `sorry` statements in your assigned file through Mathlib-compliant proofs. This code will be submitted to Mathlib and reviewed by expert mathematicians.

**Assignment:** [FILE PATH WILL BE PROVIDED]
**Current sorries:** [COUNT WILL BE PROVIDED]
**Target:** ZERO sorries

---

## **CRITICAL: READ TOOLS DOCUMENTATION FIRST**

**BEFORE ANY PROOF WORK:**

1. **Read `/Users/eric/Documents/GitHub/TDCSG/tools/CHECK_LEAN_TOOL.md` completely**
2. **Run `./check_lean.sh --help`** to see available modes
3. **Test on your file:** `./check_lean.sh --sorries YourFile.lean`
4. **Understand the modes:**
   - `--errors-only`: Fast compilation check (USE AFTER EVERY CHANGE)
   - `--sorries`: Track incomplete proofs
   - `--transparency`: Detect forbidden proof patterns
   - `--all <mode>`: Multi-file checking

**ONLY THEN begin proof work.**

---

## **MANDATORY WORKFLOW**

### **Step 1: Situational Awareness**

```bash
# Run these commands in order:
./check_lean.sh --sorries YourFile.lean        # See what you're working with
cat README.md                                   # Understand project context
./check_lean.sh --errors-only YourFile.lean    # Verify baseline compiles
```

### **Step 1b: Read ALL Imports (MANDATORY)**

**Your file imports dependencies. You MUST read them for context.**

```bash
# 1. Read your file header to see imports
head -30 YourFile.lean

# 2. Identify two types of imports:
#    - Local: import TDCSG.SomeFile
#    - Mathlib: import Mathlib.SomeModule
```

**For LOCAL imports (TDCSG.*):**
- Read the COMPLETE file
- Example: `import TDCSG.Basic` → read `TDCSG/Basic.lean` fully
- These define project-specific concepts you'll use

**For MATHLIB imports:**
- At minimum: read the module's main definitions/theorems
- Find files at: `.lake/packages/mathlib/Mathlib/[path].lean`
- Use `lean_hover` on key terms to understand APIs
- Web search: "Mathlib [ModuleName]" for documentation

**Why this matters:**
- Imports contain lemmas you'll need
- Understanding type classes prevents instance resolution errors
- Seeing proof patterns shows what tactics work
- Context prevents repeating what's already proven

**You cannot prove theorems without understanding your tools.**

### **Step 2: Work Loop**

For each sorry in your file:

1. **Read existing attempt documentation** (comment block above sorry)
2. **Design 2-3 approaches** that avoid documented failures
3. **Spawn helper agents for complex sub-problems** (see templates below)
4. **Implement proof**
5. **Test:** `./check_lean.sh --errors-only YourFile.lean`
6. **Verify persistence** (see verification box below)
7. **Document failures** if approach doesn't work
8. **Repeat until sorry eliminated**

### **Step 3: Verification After EVERY Sorry Elimination**

```
╔═══════════════════════════════════════════════════════════╗
║  MANDATORY VERIFICATION (RUN AFTER EACH SORRY):           ║
╠═══════════════════════════════════════════════════════════╣
║  1. git status --short | grep "M YourFile.lean"           ║
║     MUST SEE: M YourFile.lean                             ║
║                                                            ║
║  2. ./check_lean.sh --sorries YourFile.lean               ║
║     MUST SEE: Sorry count decreased by 1                  ║
║                                                            ║
║  3. ./check_lean.sh --errors-only YourFile.lean           ║
║     MUST SEE: ✓ No errors                                 ║
╚═══════════════════════════════════════════════════════════╝

If ANY check fails: Your edit did NOT persist. Use Edit/Write tools explicitly.
```

---

## **PARALLEL AGENT DEPLOYMENT (MANDATORY)**

### **For Parent Orchestrators:**

**YOU MUST deploy all file agents IN PARALLEL in your first response.**

```bash
# CORRECT (parallel):
Task(file1) + Task(file2) + Task(file3)  # All in ONE message

# WRONG (sequential):
Task(file1), wait for response, then Task(file2)  # Too slow!
```

**Agent Deployment Strategy:**

1. Read README.md to understand file dependencies
2. Identify ALL unblocked files (no dependency blockers)
3. Deploy agents to ALL unblocked files SIMULTANEOUSLY
4. Quick wins first: attack easy files before hard files
5. Monitor all agents concurrently

### **For File-Level Agents:**

**YOU SHOULD spawn helper agents for:**

- **Parallel proof exploration:** Test 3+ approaches simultaneously
- **Deep research:** Mathlib lemma searches, literature review
- **Sub-problems:** Independent helper lemmas, type class resolution
- **Alternative strategies:** When stuck after 2-3 failed attempts

**Expected helper agent count:** 2-5 per complex sorry, 0-1 per simple sorry

---

## **HELPER AGENT TEMPLATES**

### **Template 1: Parallel Proof Search**

```
TASK: Test multiple proof approaches for sorry at line X

Approaches to test:
1. [Tactic A + lemma set 1]
2. [Tactic B + lemma set 2]
3. [Tactic C + lemma set 3]

For each approach:
- Use lean_try_tactics to test quickly
- Report: SUCCESS/FAILURE + diagnostics + key insights

Return: Best approach or "all failed" + failure analysis
```

### **Template 2: Mathlib Lemma Research**

```
TASK: Find Mathlib lemmas for [specific mathematical concept]

Search targets:
- Pattern: [type signature or theorem shape]
- Keywords: [mathematical terms]
- Modules to check: [specific Mathlib areas]

Tools: leansearch, lean_loogle (respect 3/30s rate limit), grep

Return: List of 5-10 relevant lemmas with:
- Full name and signature
- Usage example
- Why it's relevant
```

### **Template 3: Helper Lemma Proof**

```
TASK: Prove this helper lemma needed for main theorem

lemma helper_name : [statement]

Strategy: [specific approach]

Requirements:
- Must compile cleanly
- No axioms, no fake proofs
- Verify with check_lean.sh --errors-only

Return: Complete proof or detailed blocker analysis
```

### **Template 4: Blocker Investigation**

```
TASK: Investigate why approach X failed at sorry line Y

Failed approach: [description]
Error message: [exact error from check_lean.sh]

Investigation goals:
1. Root cause analysis
2. Is this a dead end or fixable?
3. What would make this work?
4. Alternative approaches?

Tools: lean_goal, lean_diagnostics, lean_hover, web search

Return: Diagnosis + recommended next steps
```

### **Template 5: Alternative Strategy Design**

```
TASK: Design alternative proof strategies for sorry at line X

Context:
- Failed approaches: [list from documentation]
- Current blocker: [specific issue]
- Goal statement: [exact proposition]

Deliverable:
3 NEW approaches that:
- Avoid documented failures
- Use different mathematical angles
- Are testable with lean_try_tactics

Return: 3 strategies with feasibility assessment
```

---

## **CREATIVE TOOL USAGE (ENCOURAGED)**

**You have access to many tools beyond Lean. USE THEM CREATIVELY.**

### **Available Tools & Strategies:**

**🔍 Web Search (WebSearch, WebFetch):**
- Mathematical concepts: "prove [theorem name] using [technique]"
- Mathlib documentation: "Mathlib [module] API documentation"
- Research papers: Find original proofs, understand techniques
- **NO RESTRICTIONS:** Search as much as needed

**🐍 Python Scripts:**
- Numerical verification: Check theorem holds for specific values
- Symbolic computation: Use sympy/sage for algebraic manipulations
- Pattern finding: Explore mathematical relationships
- Data generation: Create test cases

**Example:**
```python
# Verify cos(2π/5) identity numerically
import numpy as np
theta = 2 * np.pi / 5
cos_val = np.cos(theta)
golden_ratio = (1 + np.sqrt(5)) / 2
expected = (golden_ratio - 1) / 2
print(f"cos(2π/5) = {cos_val}")
print(f"(φ-1)/2 = {expected}")
print(f"Match: {np.isclose(cos_val, expected)}")
```

**📄 PDF Reading Agents:**
- **Spawn an agent to read the paper** (2302.12950v1.pdf or others)
- Agent becomes a Q&A resource: "What does Theorem 2 say about E'E segment?"
- Agent can extract proofs, explain techniques, clarify definitions
- Keep agent alive for duration of session

**Example deployment:**
```
Task: Create PDF Q&A agent

Read paper: 2302.12950v1.pdf completely
Understand: Theorem 2, critical radius, GG5 construction
Role: Answer questions from other agents about:
- Paper definitions and notation
- Proof techniques used
- Geometric constructions
- How authors proved specific lemmas

Stay available for questions throughout session.
```

**🎨 Visualization & Simulation:**
- Write scripts to visualize geometric constructions
- Simulate group actions to understand behavior
- Plot functions to find relationships
- Animate transformations to build intuition

**🔬 Computer Algebra Systems:**
- Spawn agents to use Mathematica/Sage/Maple queries
- Symbolic equation solving
- Algebraic simplification
- Polynomial factorization

**🤝 Specialized Research Agents:**
- **Mathlib Expert:** Spawns and searches Mathlib for 3 hours straight
- **Literature Reviewer:** Reads 5 related papers, extracts proof techniques
- **Type Theory Consultant:** Helps resolve complex instance resolution
- **Tactic Specialist:** Tests 20 different tactic combinations

### **Creative Combinations:**

**Example 1: Cyclotomic Identity (cos 2π/5)**
```
Approach:
1. Python script: Verify numerically
2. Web search: "cyclotomic polynomial 5th root unity"
3. PDF agent: Ask "How do authors handle 5th roots in paper?"
4. Mathlib agent: Search for existing cyclotomic lemmas
5. Symbolic agent: Derive from exp(2πi/5)^5 = 1
6. Synthesis: Combine insights into Lean proof
```

**Example 2: Geometric Construction**
```
Approach:
1. Python/matplotlib: Visualize disks, segment E'E, rotation actions
2. Simulation: Verify transformations map segments correctly
3. PDF agent: "Explain Figure 3 construction in detail"
4. Numerical verification: Check distances, angles, ratios
5. Pattern recognition: Find algebraic relationships
6. Lean proof: Formalize verified insights
```

**Example 3: Unknown Technique**
```
Approach:
1. Web search: Find research papers on similar theorems
2. Spawn literature agent: Read 3 papers, extract techniques
3. Spawn implementation agent: Adapt technique to our setting
4. Test with Python: Verify approach works
5. Formalize in Lean: Use proven technique
```

### **The Rule: If It Helps, Use It**

**ENCOURAGED behaviors:**
- ✅ Spawn 5+ specialized agents for one hard sorry
- ✅ Write Python scripts to explore mathematics
- ✅ Keep PDF Q&A agent alive entire session
- ✅ Use computer algebra for complex manipulations
- ✅ Web search extensively (no limits)
- ✅ Combine multiple tools for one proof
- ✅ Think outside Lean when stuck

**Remember:**
- You're proving theorems, not just writing Lean
- Understanding the mathematics comes first
- Tools that build insight → better proofs
- Creative approaches often break through blockers

**"If a tool can help you prove the theorem, use it."**

---

## **NO BACKING DOWN PROTOCOL**

**If you encounter a "difficult" sorry:**

1. ✅ **Attempt proof** (try 2-3 approaches yourself)
2. ✅ **Spawn helper agents** (parallel exploration, research, alternatives)
3. ✅ **Deep research** (Mathlib, literature, web search)
4. ✅ **Break into sub-problems** (helper lemmas, incremental steps)
5. ✅ **Try 5 DISTINCT approaches minimum** before declaring blocker

**ONLY after 5+ serious attempts:**

If still blocked, escalate using this format:

```
BLOCKER ESCALATION

File: [exact path]
Theorem: [name] at line [number]
Statement: [exact proposition]

Blocker: [precise technical issue]

Attempts (5+ required):
1. [Approach 1]: [what happened] → [why it failed]
2. [Approach 2]: [what happened] → [why it failed]
3. [Approach 3]: [what happened] → [why it failed]
4. [Approach 4]: [what happened] → [why it failed]
5. [Approach 5]: [what happened] → [why it failed]

Research done:
- Mathlib searches: [what you searched, what you found/didn't find]
- Web searches: [queries used, results]
- Helper agents spawned: [count and outcomes]

Dependencies: [what theorems depend on this]

Proposed solutions:
- Option A: [specific approach] - Pros: [X] Cons: [Y] Feasibility: [Z]
- Option B: [specific approach] - Pros: [X] Cons: [Y] Feasibility: [Z]

USER DECISION NEEDED: [specific question]

Mark theorem in file:
/- BLOCKER: [one-line summary]
   See escalation report above for details
-/
sorry
```

**FORBIDDEN:**
- ❌ "This is too hard" (without 5 attempts)
- ❌ "This requires advanced machinery" (try to build it!)
- ❌ Silently skipping difficult sorries
- ❌ Moving on before 5 serious attempts

**This is needed for Theorem 2. If it blocks Theorem 2, we MUST solve it or escalate to user.**

---

## **ABSOLUTE RIGOR REQUIREMENTS**

### **Zero Tolerance:**

- ❌ **NO axioms** (not a single one)
- ❌ **NO admitted statements**
- ❌ **NO fake proofs:**
  - `theorem foo : True := trivial` (proves True, not real goal)
  - `def IsPredicate := True` (trivializes dependent theorems)
  - Using `trivial` except for genuinely trivial logical facts
  - Changing goal to something easy then proving that
- ❌ **NO transparency violations**

### **Transparency Check:**

**Every file MUST pass:**
```bash
./check_lean.sh --transparency YourFile.lean
```

This detects:
- Forbidden keywords: `trivial`, `admitted`, `axiom`, `unsafe`
- Forbidden patterns: `Prop := True`, `: True :=`
- Hidden sorries

**If transparency fails: Your proofs are invalid. Fix immediately.**

---

## **BUILD & TEST PROTOCOL**

### **The Sacred Rule:**

```
NEVER use `lake build` directly.
ALWAYS use `./check_lean.sh --errors-only`
```

**Why:**
- `lake build` outputs 50,000+ tokens (wastes context)
- `./check_lean.sh --errors-only` outputs 500 tokens (99% reduction)
- check_lean.sh shows COMPLETE error messages (lake clips them)
- check_lean.sh filters to YOUR file only (no noise from dependencies)

### **Iteration Loop:**

```bash
# 1. Make a change
vim YourFile.lean

# 2. Test immediately
./check_lean.sh --errors-only YourFile.lean

# 3. Interpret result
✓ No errors → SUCCESS, continue
Any errors  → FIX immediately, don't accumulate errors

# 4. After sorry eliminated, verify (see verification box above)
```

**Test after EVERY SINGLE CHANGE. Never accumulate untested changes.**

---

## **ANTI-PATTERNS (AUTO-FAIL)**

These behaviors indicate failure:

❌ **Using Mathlib lemmas without verifying they exist**
   - Check with lean_hover, leansearch, or Mathlib docs first

❌ **Claiming "too hard" without 5+ documented attempts**
   - Escalate properly or keep trying

❌ **Reporting completion without git status verification**
   - You may be working in isolated context

❌ **Using `lake build` instead of check_lean.sh**
   - Wastes tokens, clips errors

❌ **Stopping before file reaches 0 sorries**
   - "Significant progress" ≠ completion

❌ **Spawning agents sequentially when parallel is possible**
   - Deploy all at once in one message

❌ **Not reading attempt documentation above sorries**
   - Don't repeat documented failures

❌ **Erasing prior attempt documentation**
   - APPEND your attempts, never erase

---

## **DOCUMENTATION PROTOCOL**

### **When Your Approach Fails:**

Find the comment block above the sorry and ADD your attempt:

```lean
/- PROOF ATTEMPTS:
   Attempt 1: [prior attempt]
   Attempt 2: [prior attempt]
   Attempt 3: YOUR_NEW_ATTEMPT → [exact failure] | Lesson: [insight]
-/
sorry
```

**Format:** `Attempt N: [strategy] → [failure] | Lesson: [insight]`

**Keep it:**
- **Pithy:** One line per attempt
- **Specific:** Name exact tactics, lemmas, rewrites
- **Actionable:** What this rules out, what might work instead

**If no comment block exists, create one:**

```lean
/- PROOF ATTEMPTS:
   Attempt 1: [your strategy] → [failure] | Lesson: [insight]
-/
sorry
```

---

## **COMPLETION CRITERIA**

**For file-level agents:**

You are COMPLETE when:

✅ Zero sorry statements in your file
✅ Zero axioms introduced
✅ `./check_lean.sh --errors-only YourFile.lean` → ✓ No errors
✅ `./check_lean.sh --transparency YourFile.lean` → ✓ PASS
✅ Every theorem proves its stated goal (not True or wrong proposition)
✅ `git status --short` shows `M YourFile.lean`
✅ All scratch/test files cleaned up

**NOT complete:**
- "Made significant progress" (irrelevant)
- "Reduced sorries from 10 to 2" (need 0)
- "Most sorries solved" (need all)
- "Hit a blocker" (escalate properly, don't stop)

**The ONLY stopping condition is ZERO sorries.**

---

## **SCRATCH FILE PROTOCOL**

**Multiple agents work in parallel. File name conflicts WILL cause crashes.**

### **Naming Convention (MANDATORY):**

```
scratch_[unique_id]_[description].lean

Good examples:
scratch_agent_a7f3b2_ring_approach.lean
scratch_20250110_143022_type_class_test.lean
scratch_session_42_helper_lemma.lean

BAD examples (will cause conflicts):
scratch.lean          ← Multiple agents collide!
test.lean             ← Crashes
temp.lean             ← Not unique
```

### **Cleanup (MANDATORY):**

```bash
# Before completing a sorry:
rm scratch_[your_id]*.lean

# Before reporting file complete:
git status  # Must show NO scratch_*.lean files
```

**Orphaned scratch files = automatic failure.**

---

## **PARENT ORCHESTRATOR VERIFICATION**

**Before accepting agent completion, verify:**

### **Step 1: File Persistence**
```bash
git status --short | grep "M AgentFile.lean"
```
MUST see: `M AgentFile.lean`

If missing → agent's edits did NOT persist, reject immediately

### **Step 2: Sorry Count**
```bash
./check_lean.sh --sorries AgentFile.lean
```
MUST show: 0 sorries

### **Step 3: Build + Transparency**
```bash
./check_lean.sh --errors-only AgentFile.lean
./check_lean.sh --transparency AgentFile.lean
```
MUST both pass

### **Step 4: Inspect Changes**
```bash
git diff AgentFile.lean | head -100
```
Verify: Actual proof code visible (not just reports)

**If ANY check fails → re-spawn agent with explicit correction.**

---

## **QUICK REFERENCE: TOOL COMMANDS**

```bash
# Starting work
./check_lean.sh --sorries YourFile.lean        # See what to prove
./check_lean.sh --errors-only YourFile.lean    # Baseline check

# During iteration (use constantly)
./check_lean.sh --errors-only YourFile.lean    # After EVERY change

# Verification
git status --short                             # See modifications
./check_lean.sh --transparency YourFile.lean   # Quality check

# Project-wide
./check_lean.sh --all sorries TDCSG/           # Global sorry count
./check_lean.sh --all errors-only TDCSG/       # All files compile?
./check_lean.sh --all transparency TDCSG/      # All files clean?
```

---

## **PROGRESS TRACKING**

Update after each sorry:

```
SESSION PROGRESS:
├─ Sorries eliminated: X
├─ Current file sorries: Y
├─ Helper agents spawned: Z
├─ Blockers escalated: N
└─ Estimated time to completion: [your estimate]
```

---

## **FINAL MANDATE**

**Standards:**
- Mathlib publication quality (expert reviewers will examine every line)
- Uncompromising rigor (no shortcuts, no exceptions)
- Relentless persistence (0 sorries is the ONLY goal)

**Stopping conditions:**
- ✅ ONLY: Zero sorries + all verification passed
- ❌ NEVER: "too hard", "made progress", "hit blocker" (without proper escalation)

**Work philosophy:**
- Start immediately (don't plan, do)
- Parallel everything (deploy all agents at once)
- Helper agents are normal (2-5 per complex sorry)
- 5 attempts minimum (no early surrender)
- Verify constantly (git + check_lean.sh after every sorry)

**This is publication-grade mathematical formalization. Excellence is mandatory.**

---

# **BEGIN NOW.**

Read tools/CHECK_LEAN_TOOL.md, then start eliminating sorries.
