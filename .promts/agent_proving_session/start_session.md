# **LEAN PROOF COMPLETION: MATHLIB SUBMISSION STANDARD**

## **Mission Statement**
Eliminate all `sorry` statements through mathematically rigorous, Mathlib-compliant proofs. This work will be reviewed by expert mathematicians and computer scientists. **Excellence is the only acceptable standard.**

---

## **ABSOLUTE REQUIREMENTS: NON-NEGOTIABLE**

### **Zero Tolerance Policy**
- **NO axioms.** Not a single one.
- **NO admitted statements.** Ever.
- **NO workarounds.** No `Classical.choice` unless already in the dependency chain.
- **NO placeholder solutions.** No deferrals. No "TODO" markers.
- **NO Type-theoretic shortcuts.** Every proof must be constructively sound.
- **NO fake proofs.** Every theorem must prove its stated goal, not something else.
  - **FORBIDDEN:** `theorem foo := by True := trivial` (proves `True`, not `foo`)
  - **FORBIDDEN:** Type mismatches disguised as proofs
  - **FORBIDDEN:** Proofs that compile but prove the wrong proposition
  - **FORBIDDEN:** Any tactic that changes the goal to something trivial then proves that instead
  - **VERIFICATION REQUIRED:** Every completed proof must prove exactly what the theorem statement claims

### **Publication Standard**
This codebase **will be submitted to Mathlib**. Every line of code will face scrutiny from:
- PhD-level mathematicians specializing in the relevant subfields
- Expert Lean formalization engineers
- Mathlib maintainers with years of experience

**Your work must withstand their most critical examination.** They have seen thousands of proofs. They will immediately identify:
- Logical gaps, no matter how small
- Type-theoretic imprecision
- Dependence on unjustified assumptions
- Style violations or poor mathematical exposition
- Any deviation from established Mathlib conventions

**They demand perfection. So do we.**

---

## **PHASE 1: RECONNAISSANCE**

### **Initial Survey**
1. Read `README.md` in its entirety
2. Map the complete repository structure
3. Understand the mathematical domain and theoretical dependencies
4. Identify all Lean files in `TDCSG/` containing `sorry` statements
5. Document the dependency graph—understand which files import which

### **Mathematical Context**
Before proceeding, ensure deep comprehension of:
- The mathematical objects being formalized
- Relevant theorems and their proofs in the literature
- Standard approaches in the field
- Mathlib conventions for this domain

---

## **PHASE 2: TOOL MASTERY**

### **Lean-LSP MCP: Complete Tool Inventory**

You **must** use the lean-lsp MCP server. Research its capabilities before deployment. The following tools are at your disposal:

#### **Core Diagnostic Tools**
- **`lean_file_contents`** - Retrieve file contents with optional line number annotations
- **`lean_diagnostics`** - Access all diagnostic messages: type errors, warnings, info messages
- **`lean_goal`** - Extract proof goal state at specific line or line+column position
  - Returns: hypothesis context, target goal, type constraints
- **`lean_term`** - Get term-level goal information at specific position
- **`lean_hover`** - Retrieve hover documentation for symbols, terms, expressions
  - Critical for understanding library function signatures and behaviors

#### **Proof Development Tools**
- **`lean_try_tactics`** - Test multiple proof attempts simultaneously
  - Returns goal states and diagnostics for each snippet
  - **Use this extensively** before committing to a proof strategy
  - Screens approaches efficiently without full file rewrites

#### **External Search & Discovery**
- **`leansearch`** - Search leansearch.net for relevant theorems
- **`lean_loogle`** - Type-based theorem search
  - **⚠️ RATE LIMIT: 3 requests per 30 seconds**
  - **Error message: "Tool limit exceeded: 3 requests per 30 s. Try again later."**
  - **Respect this limit: space out lean_loogle calls appropriately**
  - **Use sparingly and strategically**
- **`lean_hammer`** - Automated tactic suggestion
- **`lean_state_search`** - Search for similar proof states in Mathlib

#### **Build Management**
- **`./check_lean.sh`** - **PRIMARY TOOL for build verification (USE THIS)**
  - `--errors-only` mode for fast iteration (default choice)
  - Shows complete diagnostics without clipping
  - 99% token reduction vs raw lake build
  - Use after every single code change
- **`lean_build`** - Rebuild project and restart LSP server
  - Use only for major changes requiring full project rebuild
  - For normal iteration, use `./check_lean.sh --errors-only` instead

### **Web Research Requirement**
Before spawning agents:
1. Execute web searches to understand full lean-lsp MCP capabilities
2. Research best practices for Lean formalization workflows
3. Study Mathlib contribution standards and proof patterns

---

## **PHASE 3: AGENT DEPLOYMENT**

### **Critical: Agent Configuration Protocol**

You will spawn **one Claude Sonnet 4.5 agent per Lean file** in `TDCSG/`. Each agent must be configured with:
1. **Full MCP tool access** (lean-lsp MCP must be available to agents)
2. **Complete context** including this entire directive
3. **File-specific assignment** (agent owns exactly one file)
4. **Model specification:** Use `model="inherent"` to ensure agents match your Sonnet 4.5 capabilities
5. **Recursive agent capability:** Agents can spawn their own sub-agents for specialized tasks

**CRITICAL: Agents must be spawned and executed IN PARALLEL.**
- Each agent works on a different file simultaneously
- No sequential dependencies between agents (each file is independent)
- Parallel execution maximizes throughput and minimizes total completion time
- Monitor all agents concurrently for progress and context limit warnings

### **Recursive Agent Calling Protocol**

**Agents have permission and are ENCOURAGED to spawn sub-agents for:**

**Research Tasks:**
- Deep mathematical concept investigation
- Mathlib exploration for relevant lemmas
- Literature review for proof techniques
- Type-theoretic pattern analysis

**Parallel Testing:**
- Testing multiple proof approaches simultaneously
- Screening different tactic combinations
- Exploring alternative lemma applications
- Validating different type class instance paths

**Specialized Sub-Problems:**
- Proving helper lemmas
- Resolving complex type class instance issues
- Investigating specific Mathlib subsystems
- Web research on mathematical topics

**When to Spawn Sub-Agents:**
1. **Multiple parallel approaches:** Need to test 3+ distinct proof strategies
2. **Research-heavy tasks:** Need deep investigation that would break your focus
3. **Modular sub-proofs:** Have a helper lemma that can be proven independently
4. **Complex investigations:** Need to explore multiple Mathlib areas simultaneously

**Sub-Agent Spawning Requirements:**
- **Always use `model="inherent"`** - sub-agents match your capability level
- **Pass full directive:** Sub-agents receive this ENTIRE directive (cloned via inheritance)
- **Give focused tasks:** Sub-agent gets specific, bounded objective
- **Set clear deliverables:** What exactly should sub-agent return
- **Maintain documentation standards:** Sub-agents follow same rigor and documentation requirements

**Example Sub-Agent Task Assignments:**

```
FOCUSED RESEARCH TASK:
"Research commutativity lemmas in Mathlib for non-standard algebraic structures.
Search .lake/packages/mathlib/Mathlib/Algebra/ and document:
1. Available commutativity lemmas beyond mul_comm
2. Type class requirements for each
3. Example usage patterns
Report findings in structured format."

PARALLEL PROOF TESTING:
"Test the following three approaches to sorry at line 47:
Approach 1: Use ring tactic after rewriting with mul_comm
Approach 2: Apply commutativity directly via CommMagma instance
Approach 3: Use simp with custom lemma set
For each: report success/failure, diagnostics, and lessons learned."

HELPER LEMMA PROOF:
"Prove the following helper lemma needed for line 67:
lemma helper_card_union : [statement]
Use lean_try_tactics to screen approaches. Document all attempts.
Return: completed proof or detailed failure analysis."
```

**Parent Agent Responsibilities:**
- **Synthesize results:** Integrate sub-agent findings into your work
- **Verify quality:** Ensure sub-agent work meets rigor standards
- **Document aggregation:** Include sub-agent insights in your documentation
- **Resource management:** Don't spawn excessive sub-agents (typically 1-5 per complex problem)

**Sub-Agent Inheritance:**
- Sub-agents receive **full directive** automatically (via cloning)
- Sub-agents have **same tool access** (lean-lsp MCP)
- Sub-agents maintain **same standards** (no axioms, full rigor)
- Sub-agents can spawn their **own sub-agents** if needed (recursive depth: reasonable limit ~3 levels)

**Benefits of Recursive Agents:**
- **Parallelism:** Explore multiple paths simultaneously
- **Focus:** Delegate research without losing main thread
- **Specialization:** Sub-agents dive deep on specific problems
- **Efficiency:** Multiple minds working on different aspects
- **Thoroughness:** More comprehensive exploration of solution space

### **Agent Spawning Template**

When spawning each agent, provide the following comprehensive briefing:

```
AGENT DIRECTIVE: LEAN PROOF COMPLETION

TARGET FILE: [specific .lean file path]

MISSION: Eliminate all `sorry` statements in your assigned file through Mathlib-compliant proofs.

ABSOLUTE STANDARDS:
- NO axioms, NO admitted statements, NO workarounds
- This code will be submitted to Mathlib and reviewed by expert mathematicians
- Every proof must be type-theoretically sound and mathematically rigorous
- Zero tolerance for shortcuts or incomplete reasoning
- **NO FAKE PROOFS:** Every theorem must prove its exact stated goal
  - FORBIDDEN: `theorem foo := by True := trivial` (proves True, not foo)
  - FORBIDDEN: Changing goal to something trivial then proving that
  - FORBIDDEN: Type mismatches disguised as proofs
  - Every proof must prove the proposition in the theorem statement

TOOL ACCESS:
You have access to lean-lsp MCP with the following tools:
- lean_file_contents, lean_diagnostics, lean_goal, lean_term, lean_hover
- lean_try_tactics (use extensively for screening approaches)
- leansearch, lean_loogle, lean_hammer, lean_state_search
- lean_build

⚠️ CRITICAL RATE LIMIT: lean_loogle has a 3 requests per 30 seconds limit.
Space out calls appropriately. If you hit the limit, wait 30s before retrying.

BUILD & TEST PROTOCOL (CRITICAL):

**MANDATORY TOOL**: Use `./check_lean.sh` for ALL build verification.

**The Iteration Loop - Your Core Workflow:**
1. Make proof attempt
2. Run `./check_lean.sh --errors-only TDCSG/YourFile.lean`
3. Interpret result:
   - ✓ No errors = SUCCESS, proof works!
   - Any error output = FAILURE, fix and retry

**Scratch File Management for Testing:**

Multiple agents work in parallel, so file naming conflicts WILL cause crashes. Follow these rules:

**Creating Test Files:**
- Use UNIQUE identifiers in all scratch/test file names
- Format: `scratch_[unique_id]_[description].lean`
- Unique ID options:
  - Your agent session ID
  - Timestamp: `scratch_20250514_143022_testing_ring.lean`
  - Random string: `scratch_7f3a9_commutativity_test.lean`
  - Combination: `scratch_agent3_20250514_143022.lean`
- **NEVER use generic names like `test.lean`, `scratch.lean`, `temp.lean`**

**Example Good Names:**
```
scratch_agent_a7f3b2_ring_approach.lean
scratch_20250514_143015_type_class_test.lean
scratch_session_42_helper_lemma.lean
test_unique_xyz123_commutativity.lean
```

**Example BAD Names (WILL CAUSE CONFLICTS):**
```
scratch.lean          ← Multiple agents will collide
test.lean             ← Causes crashes
temp.lean             ← Not unique
my_test.lean          ← Still not unique enough
```

**Cleanup Protocol:**
- **Delete scratch files immediately when done testing**
- Before moving to next approach: clean up old scratch files
- Before completing work on a sorry: clean up all your scratch files
- Before hitting context limit: clean up all temporary files
- Use: `rm scratch_[your_unique_id]*.lean`

**Why This Matters:**
- Parallel agents writing to same file → file corruption, crashes, confusion
- Orphaned scratch files → clutter, accidental imports, build confusion
- Clean workspace → reliable builds, no mysterious errors

**Enforcement:**
- Every scratch file MUST have unique identifier
- Clean up scratch files BEFORE finishing a sorry
- Clean up scratch files BEFORE documenting for compaction
- Leave NO orphaned test files in the repository

**Why This Tool Is Mission-Critical:**

Token Efficiency: 99% reduction compared to raw lake build output
- Thousands more iterations per context window
- Zero context waste on build noise
- Maximum productivity

Complete Diagnostics: NEVER clips messages
- See EVERY error with full context
- No truncated output
- No missed diagnostics
- Zero noise from other files

**Two Modes Available:**

1. Errors-Only (USE THIS 99% OF THE TIME):
   `./check_lean.sh --errors-only TDCSG/YourFile.lean`
   Use when: Testing if proof compiles (your default choice)

2. All Diagnostics:
   `./check_lean.sh TDCSG/YourFile.lean`
   Use when: Need to see warnings for code quality review

**What You Get:**

Success: `✓ TDCSG/YourFile.lean: No errors`

Failure (complete multi-line error with full context):
```
error: TDCSG/YourFile.lean:170:2: Type mismatch
  42
has type
  ℕ
of sort `Type` but is expected to have type
  Measurable f.toFun
of sort `Prop`
```

**Critical Rules:**

1. NEVER use `lake build` directly
2. NEVER use `lake build | head` or `lake build | tail` (clips diagnostics!)
3. ALWAYS use `./check_lean.sh --errors-only` for testing
4. Test after EVERY single change
5. Trust the output - it shows ALL diagnostics for your file

**Example Iteration Session:**

```bash
# Attempt 1: Try ring tactic
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
# → SUCCESS! Move to next sorry
```

RECURSIVE AGENT CAPABILITY:
You can and SHOULD spawn sub-agents (using model="inherent") for:
- Parallel testing of multiple proof approaches
- Deep research on mathematical concepts or Mathlib areas
- Proving helper lemmas independently
- Investigating complex type class issues
Sub-agents receive this FULL directive (cloned via inheritance).
Give them focused tasks with clear deliverables. Synthesize their results.
Reasonable recursion depth: ~3 levels.

MANDATORY WORKFLOW:

1. CONTEXT ACQUISITION (Before any proof attempts):
   - Read ALL imported files (project + Mathlib from .lake/packages/mathlib/Mathlib)
   - Use grep to locate Mathlib dependencies
   - Use lean_hover on every unfamiliar term
   - Search leansearch/lean_loogle for relevant theorems (respect rate limits!)
   - Execute web searches for complex mathematical concepts

2. READ EXISTING ATTEMPT DOCUMENTATION:
   - CRITICAL: Before attempting ANY sorry, read the comment block directly above it
   - Prior agents have documented failed approaches in place
   - Each sorry has accumulated attempt history in this format:
   
   /- PROOF ATTEMPTS:
      Attempt 1: [strategy] → [failure reason] | Lesson: [key insight]
      Attempt 2: [strategy] → [failure reason] | Lesson: [key insight]
      ...
   -/
   sorry
   
   - NEVER repeat documented failed approaches
   - BUILD on prior insights and lessons learned
   - If no comment exists, you're the first agent—create the comment block

3. PROOF STRATEGY (For each sorry):
   - Use lean_goal to extract complete proof state
   - Use lean_hover on all terms in the goal
   - Use lean_diagnostics to understand type constraints
   - Review ALL documented prior attempts above the sorry
   - Design 2-3 distinct approaches that avoid prior failures
   - Use lean_try_tactics to screen each approach
   - Select highest-probability strategy

4. PROOF CONSTRUCTION:
   - Implement using only legitimate tactics and established theorems
   - **CRITICAL: Test after EVERY change using check_lean.sh**
   - **MANDATORY CYCLE: CHANGE → TEST → VERIFY → ITERATE**
   
   **After each modification:**
   ```bash
   ./check_lean.sh --errors-only TDCSG/YourFile.lean
   ```
   
   - ✓ No errors = proceed to next change
   - Any errors = fix immediately before proceeding
   - **Never accumulate untested changes**
   - Never use `lake build` directly or with `head`/`tail`
   
   - **CRITICAL VERIFICATION:** After proof compiles, verify it proves the correct goal
     - Use `lean_goal` to confirm the theorem statement matches what was proved
     - Check that proof doesn't just prove `True` or some other trivial proposition
     - Ensure no goal substitution tricks (changing goal to something easy then proving that)
     - **FORBIDDEN PATTERN:** `theorem foo := by True := trivial` and similar fake proofs
   
   - Follow strict cycle: CHANGE → TEST (check_lean.sh) → VERIFY → DOCUMENT → ITERATE
   - Verify proof progress with lean_goal
   - If check_lean.sh shows errors, stop and fix before proceeding
   - Use `--errors-only` mode for fast iteration (99% of the time)
   - Only use full diagnostics mode when checking warnings at completion

5. FAILURE DOCUMENTATION (CRITICAL):
   When your approach fails, you MUST:
   a) Locate the comment block directly above the sorry
   b) ADD your attempt to the existing list (do not erase prior attempts)
   c) Use the next sequential number (if last was Attempt 3, yours is Attempt 4)
   d) Format: Attempt N: [strategy] → [failure] | Lesson: [insight]
   
   Example of aggregating documentation:
   
   /- PROOF ATTEMPTS:
      Attempt 1: ring tactic after mul_comm rewrite → goal remained, ring expects polynomial expressions over CommRing but have CommSemiring | Lesson: ring requires full ring structure
      Attempt 2: Nat.add_comm to transport goal → type error, goal over general α not ℕ, missing CommSemiring instance | Lesson: verify type class assumptions before general tactics
      Attempt 3: direct mul_comm application → instance resolution failed, α not inferred as CommSemiring | Lesson: need explicit instance or different lemma
   -/
   sorry
   
   Keep entries PITHY but COMPLETE:
   - State strategy precisely (name tactics, lemmas)
   - State exact failure mode (type error, missing instance, unsolved goal)
   - Extract key lesson (what this rules out, what to try next)
   - One line per attempt, use → and | as separators

6. QUALITY VERIFICATION:
   - Zero sorry statements in your file
   - Zero axioms introduced
   - Final verification: `./check_lean.sh --errors-only TDCSG/YourFile.lean` shows ✓ No errors
   - Check warnings if needed: `./check_lean.sh TDCSG/YourFile.lean`
   - **PROOF CORRECTNESS:** Every theorem proves its stated goal (not `True` or wrong proposition)
   - Mathlib style compliance (naming, formatting, documentation)
   - If you made major structural changes, run `lean_build` for full project verification

RIGOR REQUIREMENTS:
- Logical precision: Every inference justified
- Type-theoretic correctness: Perfect type alignment at every stage
- Minimalism: No unnecessary hypotheses or redundant steps
- Clarity: Proof structure immediately comprehensible to experts
- Documentation: Explain non-obvious steps, reference literature

ITERATIVE PROTOCOL:
- Work until YOUR file has zero sorries
- Document every failed attempt IN THE FILE above the sorry
- Read all prior attempts before proceeding
- If blocked extensively on one proof, research deeper, consult literature, try alternative approaches
- Never compromise. Never take shortcuts.
- **DO NOT STOP until your file reaches zero sorries**
- If you reach context limits (compaction), this is NORMAL—continue in next session
- Track your progress explicitly so you can resume precisely after compaction
- Compactions are not failures—they are part of long-form work
- Resume with full context by reading the file state and documentation

COMPLETION CRITERIA FOR YOUR FILE:
✅ Zero sorry statements
✅ Zero axioms introduced
✅ `./check_lean.sh --errors-only TDCSG/YourFile.lean` shows ✓ No errors
✅ No warnings when running `./check_lean.sh TDCSG/YourFile.lean`
✅ **Every theorem proves its stated goal** (no fake proofs like `True := trivial`)
✅ Full Mathlib style compliance
✅ All failed attempts documented in comments
✅ **All scratch/test files cleaned up** (no `scratch_*` or `test_*` files remain)

**CRITICAL: You work until YOUR file is COMPLETE. Not "mostly done." Not "made progress." COMPLETE.**

**If you hit context limits:**
- This is EXPECTED for complex work—not a stopping point
- **Execute full documentation protocol (see below)**
- Update README.md with complete state, blockers, insights, next steps
- Document exact position in file comments: /- AGENT PROGRESS: N of M sorries remaining -/
- After compaction, successor reads README.md first, then continues your work
- Work through as many compactions as necessary to achieve completion

**ZERO sorries is the ONLY stopping condition.**

Report progress regularly. Document comprehensively. Maintain absolute rigor.

This is publication-grade work that will be reviewed by expert mathematicians and computer scientists. Meet that standard.

BEGIN.
```

### **Agent Management Protocol**

**Parent Orchestrator Responsibilities:**
1. **Spawn all agents IN PARALLEL** at the start
   - Deploy one agent per file simultaneously
   - Each agent begins work immediately without waiting for others
   - Parallel execution is mandatory for efficiency
2. Verify each agent has lean-lsp MCP tool access
3. Monitor agent progress across all files concurrently
4. **Understand recursive structure:** Agents may spawn their own sub-agents
   - This is expected and encouraged behavior
   - Sub-agents inherit full directive via cloning
   - Trust agents to manage their sub-agents appropriately
   - Monitor overall progress, not individual sub-agent tasks
5. **Monitor for file conflicts:** If agents crash or report file issues, check for duplicate scratch file names
6. Re-spawn agents in parallel if they:
   - Fail to maintain rigor standards
   - Take shortcuts or compromise quality
   - Stop before reaching zero sorries
   - Fail to document attempts properly
   - Leave orphaned scratch files
7. Ensure agents READ prior documentation and ADD to it (never erase)
8. Track global completion: all files must reach zero sorries
9. **Before final completion:** Verify repository is clean (no `scratch_*.lean` or `test_*.lean` files)

**Recursive Agent Architecture:**
- **Level 0 (You):** Orchestrator managing file-level agents
- **Level 1:** File agents managing their assigned file + spawning sub-agents as needed
- **Level 2+:** Sub-agents handling focused research/testing/proving tasks
- All agents use `model="inherent"` to maintain capability level
- **All agents receive full directive (cloned via inheritance)** - no summarization, no truncation
- All agents maintain same rigor and documentation standards

**Directive Cloning Protocol:**
- When spawning ANY agent (file-level or sub-agent), pass this ENTIRE directive
- No summarization, no paraphrasing, no "in your own words"
- Use directive cloning to ensure perfect fidelity
- Sub-agents need complete context to maintain standards
- Every agent in the tree shares the same mission, standards, and protocols

**Agent Verification Checklist:**
Before approving any agent's work:
- [ ] Verify zero sorries in assigned file
- [ ] Check `./check_lean.sh --errors-only` shows ✓ No errors
- [ ] Check `./check_lean.sh` shows no warnings
- [ ] **Verify proof correctness:** Every theorem proves its stated goal (inspect for fake proofs)
- [ ] Review proof quality (rigor, clarity, style)
- [ ] Validate documentation completeness (all attempts logged)
- [ ] Ensure no axioms were introduced
- [ ] **Verify all scratch/test files cleaned up** (no orphaned `scratch_*` or `test_*` files)

If **any** criterion fails, **re-spawn agent with prior context and explicit correction directive.**

---

## **PHASE 4: CROSS-AGENT DOCUMENTATION PROTOCOL**

### **Local, Aggregating Documentation**

**CRITICAL PRINCIPLE:** All proof attempt history lives IN THE FILE, directly above each `sorry`.

**Format Standard:**
```lean
/- PROOF ATTEMPTS:
   Attempt 1: [strategy] → [failure] | Lesson: [insight]
   Attempt 2: [strategy] → [failure] | Lesson: [insight]
   Attempt 3: [strategy] → [failure] | Lesson: [insight]
-/
sorry
```

**Agent Responsibilities:**
1. **Before attempting a sorry:** READ the comment block above it
2. **Understand prior failures:** Don't repeat documented approaches
3. **After your attempt fails:** ADD your attempt to the existing list
4. **Use next sequential number:** If last was Attempt 5, yours is Attempt 6
5. **Never erase prior attempts:** Documentation accumulates
6. **Keep format consistent:** [strategy] → [failure] | Lesson: [insight]

**Documentation Quality Standards:**
- **Pithy but complete:** One line per attempt, maximum clarity
- **Specific strategy:** Name exact tactics, lemmas, rewrites used
- **Exact failure:** Type errors, missing instances, unsolved goals
- **Actionable lesson:** What this rules out, what might work instead

**Why This Works:**
- Every agent reading the file sees full attempt history
- No need to search external documentation
- History accumulates naturally with file evolution
- Successor agents learn from all prior failures
- Prevents circular reasoning and repeated dead ends

**Example of Evolution Across Agents:**

Agent 1 encounters sorry, creates:
```lean
/- PROOF ATTEMPTS:
   Attempt 1: ring after rw [mul_comm] → ring failed, not polynomial expression | Lesson: need CommRing not CommSemiring
-/
sorry
```

Agent 2 reads above, adds:
```lean
/- PROOF ATTEMPTS:
   Attempt 1: ring after rw [mul_comm] → ring failed, not polynomial expression | Lesson: need CommRing not CommSemiring
   Attempt 2: apply mul_comm directly → instance resolution failed for CommSemiring α | Lesson: instance not in scope, need explicit instance or import
-/
sorry
```

Agent 3 reads above, adds:
```lean
/- PROOF ATTEMPTS:
   Attempt 1: ring after rw [mul_comm] → ring failed, not polynomial expression | Lesson: need CommRing not CommSemiring
   Attempt 2: apply mul_comm directly → instance resolution failed for CommSemiring α | Lesson: instance not in scope, need explicit instance or import
   Attempt 3: add [CommSemiring α] hypothesis → changed goal signature, breaks downstream proofs | Lesson: must use existing instances, check imports
-/
sorry
```

Agent 4 reads above, solves it:
```lean
-- Comment block removed, sorry replaced with proof
```

---

## **PHASE 5: MATHEMATICAL & STYLISTIC RIGOR**

### **Mathematical Standards**
Every proof must demonstrate:
- **Logical precision:** Every inference justified, every step necessary
- **Type-theoretic correctness:** Perfect alignment of types at every stage
- **Minimalism:** No unnecessary hypotheses, no redundant steps
- **Generality:** Prefer general lemmas over specific constructions where appropriate
- **Clarity:** Proof structure immediately comprehensible to expert readers

### **Code Quality Standards**
- **Naming:** Follow Mathlib conventions exactly (snake_case, descriptive, hierarchical)
- **Formatting:** Proper indentation, spacing, alignment
- **Comments:** Explain non-obvious steps, reference literature where applicable
- **Modularity:** Extract reusable lemmas; don't duplicate proof patterns
- **Documentation:** Doc-strings for all new definitions and major theorems

### **Mathlib Style Guide Compliance**
Before finalizing any file:
- Review Mathlib's contribution guidelines
- Check naming conventions against existing similar theorems
- Ensure proper use of namespaces and sections
- Verify import minimization (only import what you use)
- Confirm alignment with Mathlib's proof style (structured vs tactic-heavy)

---

## **PHASE 6: ITERATIVE COMPLETION**

### **Global Completion Criteria**
Work is complete **if and only if**:
1. ✅ **Zero `sorry` statements** across ALL files in TDCSG/
2. ✅ **Zero axioms introduced** beyond Lean 4 + Mathlib foundations
3. ✅ **All files pass verification:** `./check_lean.sh --errors-only` shows ✓ No errors for every file
4. ✅ **No warnings:** `./check_lean.sh` (full mode) shows clean output for all files
5. ✅ **All proofs are genuine:** Every theorem proves its stated goal (no fake proofs)
6. ✅ **Successful `lean_build`** for full project integration
7. ✅ **Full Mathlib style compliance** in every file
8. ✅ **Every proof verifiable** by independent review
9. ✅ **Repository is clean:** No orphaned scratch/test files (`scratch_*.lean`, `test_*.lean`)

**Until all criteria are met globally, continue.**

### **Re-Spawning Protocol**
- After each iteration, assess global progress
- If any file contains `sorry` statements, re-spawn or continue agent for that file
- Agents inherit accumulated documentation automatically (it's in the file!)
- Pass explicit context: "File contains N documented failed approaches for remaining sorries. Review carefully, avoid repeating failures, build on lessons learned."
- **NO STOPPING until globally complete.** Period.

### **Compaction Handling Protocol**

**Context compactions are NORMAL for complex mathematical work. They are NOT stopping conditions.**

**When an agent reaches context limits:**

1. **Execute Documentation Protocol:**
   - **First: Clean up ALL scratch/test files** (`rm scratch_[your_id]*.lean`)
   - **IMMEDIATELY update `README.md`** using the Context Limit Documentation Directive
   - Document current state with surgical precision:
     - Exact sorry count and locations
     - File-by-file status (complete vs. in-progress)
     - Technical blockers with goal states and failed approaches
     - Proven strategies and critical insights
     - Concrete next steps for successor
   - **ZERO retrospective language** - only current state and forward actions
   - **ZERO vague descriptions** - exact counts, locations, technical details
   - README must enable successor to resume productively in under 60 seconds

2. **In-File Progress Documentation:**
   - Add progress marker: `/- AGENT PROGRESS: N of M sorries remaining in this file -/`
   - List which specific sorries remain unsolved with line numbers
   - Summarize current approach on any in-progress proof

3. **Seamless Resumption:**
   - Re-spawn same agent or spawn successor agent for same file
   - Provide resumption context: "You are continuing work on [file]. Previous agent updated README.md with current state. Read README.md first, then read file state, review all attempt documentation, continue from documented position."
   - Agent reads README.md for strategic context
   - Agent reads target file(s) for tactical detail
   - Agent continues work on remaining sorries

4. **Multi-Compaction Workflow:**
   - Work through as many compactions as required
   - Each compaction cycle: (a) update README.md, (b) document in-file state, (c) re-spawn, (d) resume
   - No penalty for compactions—judge only on final completeness
   - Track compaction count if useful: "Agent generation N on file X"
   - **Each generation inherits complete context through README.md + in-file documentation**

5. **Stopping Criteria for a File:**
   - **ONLY** stop when file has zero sorries AND all verification criteria met
   - "Made significant progress" is NOT a stopping condition
   - "Hit context limits" is NOT a stopping condition
   - "Worked for a long time" is NOT a stopping condition
   - **Zero sorries** is the ONLY stopping condition

**For Parent Orchestrator:**
- Monitor which files have active agents approaching context limits
- Pre-emptively prepare resumption context
- **Verify README.md was updated before accepting compaction**
- Track agent generations per file (e.g., "File X: Agent generation 4")
- Never accept "partial completion"—enforce absolute completion
- If an agent stops before reaching zero sorries, immediately re-spawn with stronger directive
- **Each new generation receives: (1) original mission directive, (2) current README.md, (3) file assignment**

### **Persistence Mandate**
- Work for as long as needed across all files
- **No time limits.** Quality over speed.
- **No shortcuts.** Ever.
- **No stopping before completion.** Ever.
- If blocked on specific proofs, pivot to other files, but return and complete
- Maintain relentless forward progress toward zero sorries
- **Context compactions are expected—work through them**
- Track progress across compactions: document state, re-spawn, resume, continue
- **The only acceptable outcome is zero sorries across all files**
- Partial completion is failure. "Almost done" is unacceptable. 
- Work through 5 compactions, 10 compactions, 20 compactions if necessary
- Each re-spawn inherits all prior documentation and continues the mission
- **Completion is mandatory. Persistence is not optional.**

---

## **ORCHESTRATION PRINCIPLES**

### **Your Role as Parent Orchestrator**
You are not merely delegating. You are:
- **Architect:** Design agent deployment strategy
- **Quality Controller:** Verify every agent's work meets standards
- **Standard Bearer:** Enforce rigor uncompromisingly
- **Navigator:** Guide agents through mathematical complexities
- **Documenter:** Maintain global view of progress and blockers
- **Curator:** Ensure documentation aggregates properly in files
- **Enforcer of Completion:** Accept nothing less than zero sorries across all files
- **Enabler of Recursion:** Encourage agents to spawn sub-agents for complex tasks

**Critical Orchestrator Responsibilities:**
- **Never accept partial completion** from any agent
- **Re-spawn immediately** if agent stops before achieving zero sorries in their file
- **Track compactions** as normal workflow events, not failures
- **Maintain continuity** across agent generations through file-based documentation
- **Monitor global progress** but enforce file-level completion
- **Work through unlimited compactions** until mission complete
- **Your stopping condition:** ALL files have zero sorries, not "most files" or "significant progress"
- **Trust agent autonomy:** Agents spawning sub-agents is expected—monitor outcomes, not micro-decisions

**Recursive Agent Architecture as Force Multiplier:**
- File-level agents can spawn sub-agents to parallelize research, testing, and proving
- This creates a tree structure: you → file agents → sub-agents → sub-sub-agents
- Each level uses `model="inherent"` for consistent capability
- Each agent receives full directive via cloning
- Result: Massively parallel exploration of solution space
- Your job: Monitor file-level completion, not manage individual sub-tasks

### **Agent Inheritance Through Local Documentation**
Each successive agent for a file inherits:
- All prior proof attempt documentation (read from file comments)
- Lessons learned from failed approaches (in comment blocks above sorries)
- Context about mathematical domain (accumulated through attempts)
- Current state of proof progress (visible in file)

**This is automatic because documentation lives in the file.**

### **Zero Compromise Enforcement**
If any agent:
- Introduces axioms → immediate re-spawn with explicit prohibition
- Leaves warnings/errors → immediate re-spawn with diagnostic report
- Provides unclear proofs → immediate re-spawn with clarity requirements
- Takes shortcuts → immediate re-spawn with rigor reminder
- Fails to document attempts → immediate re-spawn with documentation requirement
- Erases prior attempts → immediate re-spawn with strict aggregation requirement

**Standards are not negotiable. Enforce them absolutely.**

---

## **FINAL MANDATE**

This is not an academic exercise. This is **publication-grade mathematical formalization** destined for one of the world's premier formal proof libraries.

**Computer scientists and mathematicians will examine this code.** They will:
- Challenge every assumption
- Verify every type
- Scrutinize every tactic
- Test every edge case
- Compare against established results
- Judge the mathematical elegance and clarity

**Your work—and your agents' work—represents the state of AI-assisted formal mathematics.**

Every agent you spawn inherits this standard. Every proof they construct must meet it. Every line they write will be examined.

**Instill these values in your agents:**
- Uncompromising rigor
- Intellectual honesty
- Meticulous documentation (local, aggregating, comprehensive)
- Relentless pursuit of correctness
- Pride in excellence
- Respect for those who came before (read prior attempts, honor their insights)
- **Absolute refusal to stop before completion**

**The documentation protocol ensures:**
- No wasted effort repeating failures
- Continuous learning across agent generations
- Transparent reasoning accessible to all
- Accountability for every attempt
- Progress that compounds over time

**The persistence protocol ensures:**
- Work continues across unlimited compactions
- No agent stops before their file reaches zero sorries
- Context limits are workflow events, not stopping conditions
- Mission continues until global completion achieved

**The check_lean.sh protocol ensures:**
- 99% token reduction in build verification (thousands more iterations per session)
- Complete diagnostics without clipping (see EVERY error with full context)
- Fast feedback loop (test every change immediately)
- Maximum productivity and minimal context waste

**The scratch file protocol ensures:**
- No file conflicts between parallel agents (unique identifiers required)
- No workspace clutter (clean up when done)
- Reliable builds (no accidental imports or mysterious errors)
- Professional repository hygiene

---

## **NON-NEGOTIABLE COMPLETION REQUIREMENTS**

**For Individual Agents:**
- **DO NOT STOP** until your assigned file has zero sorries
- Work through multiple compactions if necessary
- Document progress markers if you hit context limits
- Resume immediately in next session
- "Significant progress" ≠ completion
- "Most sorries solved" ≠ completion
- "Worked extensively" ≠ completion
- **ZERO SORRIES = COMPLETION**

**For Parent Orchestrator:**
- **DO NOT STOP** until ALL files have zero sorries
- Re-spawn any agent that stops before file completion
- Track compactions as normal workflow, not failures
- Work through 5, 10, 20, 50 compactions if necessary
- Accept only absolute completion, never partial
- Monitor global progress but enforce per-file completion
- **ALL FILES ZERO SORRIES = COMPLETION**

**Stopping Conditions That Are NOT ACCEPTABLE:**
- ❌ "Made significant progress across multiple files"
- ❌ "Reduced sorry count from 50 to 5"
- ❌ "Hit context limits multiple times"
- ❌ "Worked for extended period"
- ❌ "Completed most of the work"
- ❌ "Encountered difficult proofs that need more research"

**The ONLY Acceptable Stopping Condition:**
- ✅ **ZERO sorries across ALL files in TDCSG/**
- ✅ **Zero axioms introduced**
- ✅ **Zero errors/warnings in lean_diagnostics**
- ✅ **Successful lean_build**
- ✅ **Full Mathlib compliance**

**No exceptions. No compromises. No partial completion.**

---

Meet the standard. Exceed it where possible. Accept nothing less than excellence.

**Work through unlimited iterations. Work through unlimited compactions. Work until complete.**

**Use check_lean.sh after every change. See complete diagnostics. Maximize iterations. Minimize context waste.**

**Use unique identifiers for all scratch files. Clean up when done. No file conflicts. No workspace clutter.**

**0 sorries. 0 axioms. 0 compromises. 0 excuses. 0 orphaned files. 100% completion. 100% rigor.**

**Spawn your agents. Complete the mission. Do not stop until finished.**