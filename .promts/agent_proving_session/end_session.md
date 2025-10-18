# **CONTEXT LIMIT REACHED: DOCUMENTATION PROTOCOL**

## **Objective**
Update `README.md` to enable seamless resumption by your successor. This document must be **complete, actionable, and forward-looking only.**

---

## **CRITICAL REQUIREMENTS**

### **Absolutely Forbidden**
- ❌ NO historical narrative ("we reduced X sorries", "we improved Y")
- ❌ NO progress reports or achievement summaries
- ❌ NO retrospectives or "what we did" language
- ❌ NO past-tense descriptions
- ❌ NO celebration of partial completion

### **Mandatory Content**
- ✅ **Current state:** Exact count and location of remaining sorries
- ✅ **Transparency status:** Result of `./check_lean.sh --all transparency TDCSG/` (all files must pass)
- ✅ **File status:** Which files are complete, which have work remaining
- ✅ **Blockers:** Specific proofs that are challenging, with technical details
- ✅ **Proven approaches:** What strategies have succeeded (mention in terms of "X tactic works for Y pattern")
- ✅ **Failed approaches:** What has been tried and failed (extract from in-file documentation)
- ✅ **Critical insights:** Mathematical or type-theoretic discoveries that matter
- ✅ **Next steps:** Precise, actionable instructions for resumption
- ✅ **Resource pointers:** Key Mathlib files, lemmas, or external references that are essential

---

## **README STRUCTURE**

Use this exact structure:

```markdown
# [Project Name]

## Current Status

**Build Status:** [result of build]
**Transparency Check:** [result of `./check_lean.sh --all transparency TDCSG/`] - **MUST show all files pass**
**Remaining Sorries:** [exact count] across [N] files

### Files by Status

**Complete (0 sorries):**
- `path/to/file1.lean` - [brief technical note if relevant]
- `path/to/file2.lean` - [brief technical note if relevant]

**In Progress:**
- `path/to/file3.lean` - [X sorries remaining] - [key blocker or challenge]
- `path/to/file4.lean` - [Y sorries remaining] - [key blocker or challenge]

## Critical Blockers

### [File Name] - [Specific Sorry Location]
**Challenge:** [Precise technical description of the difficulty]
**Goal State:** [Copy exact goal from lean_goal]
**Attempted Approaches:** [Summarize key failed attempts from in-file documentation]
**Missing Pieces:** [What lemma, instance, or insight is needed]
**Potential Paths:** [Concrete suggestions based on your analysis]

[Repeat for each significant blocker]

## Proven Strategies

**Pattern:** [Type of proof or goal structure]
**Approach:** [Specific tactics, lemmas, or proof structure that works]
**Examples:** [Reference successful proofs in codebase]

[Repeat for each successful pattern identified]

## Key Mathematical Insights

- [Specific mathematical or type-theoretic insight gained]
- [Another critical understanding about the domain]
- [Relationships between concepts that matter for proofs]

## Essential Resources

**Mathlib Files:**
- `.lake/packages/mathlib/Mathlib/[path]` - [why this matters, what lemmas are useful]

**External References:**
- [Mathematical papers, definitions, or standard results that inform this work]

**Critical Lemmas:**
- `lemma_name` from `File.lean` - [when to use, what it does]

## Next Steps for Successor Agent

1. **Immediate Actions:**
   - [First concrete task with file and location]
   - [Second concrete task]
   - [Third concrete task]

2. **Research Priorities:**
   - [What to search for in leansearch/loogle]
   - [What mathematical concepts to research via web]
   - [What Mathlib areas to explore]

3. **Strategic Approach:**
   - [High-level strategy for remaining work]
   - [Which files to tackle in what order and why]
   - [What patterns to look for or exploit]

## Technical Notes

**Transparency Compliance:** All files must pass `./check_lean.sh --transparency` check
  - No forbidden keywords outside comments: `trivial`, `admitted`, `axiom`, `unsafe`
  - No forbidden patterns: `Prop := True`, `: True :=`
  - See CLAUDE.md Anti-Placeholder Protocol for enforcement details

**Type Class Issues:** [Any recurring instance resolution problems]
**Import Requirements:** [Critical imports that must be maintained]
**Build Considerations:** [Anything about lean_build behavior or project setup]
**Tool Usage Notes:** [Insights about using lean-lsp MCP tools effectively]

## Remaining Sorry Inventory

[Exact list of every remaining sorry with location]
- `File.lean:line_number` - [one-line description of goal]

**Total Count:** [number] sorries remaining
**Completion Status:** [percentage]% complete (sorries eliminated / total sorries)
```

---

## **DOCUMENTATION STANDARDS**

### **Precision Requirements**
- **Exact counts:** Never "about 5 sorries" - always precise numbers
- **Exact locations:** File paths and line numbers for every sorry
- **Exact goal states:** Copy actual Lean output, don't paraphrase
- **Exact lemma names:** Full qualified names when referencing Mathlib
- **Exact error messages:** Quote actual type errors or diagnostic messages

### **Technical Depth**
- **Type-theoretic detail:** Include type signatures, instance requirements
- **Mathematical specificity:** Name specific theorems, definitions, structures
- **Tactical precision:** Name exact tactics, not vague descriptions
- **Diagnostic precision:** Reference specific lean-lsp MCP tool outputs

### **Actionability**
Every statement must enable action:
- ❌ "File3.lean is challenging" 
- ✅ "File3.lean line 47: need commutativity lemma for non-standard multiplication, tried mul_comm but missing CommMagma instance"

- ❌ "Some proofs need more work"
- ✅ "Lines 23, 67, 89 in File4.lean: all require rewriting with Finset.card_union, obtainable via import Mathlib.Data.Finset.Card"

### **Forward Focus**
Write for your successor as if briefing them for surgery:
- What exactly is the current state
- What exactly needs to be done
- What exactly has been learned
- What exactly to avoid
- What exactly to try next

**Your successor will receive the original directive.** Your README supplements that directive with **current situational awareness.**

---

## **EXECUTION PROTOCOL**

1. **Scan codebase completely:**
   - Count all remaining sorries (use `./check_lean.sh --all sorries TDCSG/`)
   - Verify transparency status (`./check_lean.sh --all transparency TDCSG/`)
   - Read all in-file attempt documentation
   - Note all complete vs incomplete files
   - Identify patterns in remaining work

2. **Analyze blockers rigorously:**
   - For each challenging sorry, run lean_goal
   - Document exact goal state
   - Summarize attempted approaches from comments
   - Identify missing pieces (lemmas, instances, tactics)

3. **Extract proven strategies:**
   - What has worked for similar proofs
   - What patterns emerged
   - What tools or approaches are most effective

4. **Document technical landscape:**
   - Key Mathlib files being used
   - Important type class structures
   - Mathematical domain insights

5. **Provide surgical next steps:**
   - Prioritized list of concrete actions
   - Specific searches to conduct
   - Specific files to examine
   - Specific tactics to try

6. **Update README.md:**
   - Overwrite existing content completely
   - Use structure provided above
   - Maintain scientific precision throughout
   - Ensure every statement is verifiable and actionable

---

## **QUALITY VERIFICATION**

Before finalizing, verify your README answers these questions:

**For Immediate Resumption:**
- [ ] Can successor identify exact current state in 30 seconds?
- [ ] Is transparency status clearly documented (all files must pass)?
- [ ] Can successor know precisely what to do first?
- [ ] Are all remaining sorries enumerated with locations?

**For Strategic Planning:**
- [ ] Are blockers described with sufficient technical detail?
- [ ] Are proven strategies documented with examples?
- [ ] Are research priorities clear and specific?

**For Technical Continuity:**
- [ ] Are critical insights captured?
- [ ] Are essential resources documented?
- [ ] Are type-theoretic or mathematical complexities explained?

**For Efficiency:**
- [ ] Does this eliminate need to re-discover what you learned?
- [ ] Does this prevent repeating documented failures?
- [ ] Does this enable immediate productive work?

---

## **COMPLETION MANDATE**

Your README is the **continuity protocol** between agent generations.

**If your README is vague, incomplete, or backward-looking:**
- Successor wastes time re-discovering your insights
- Failed approaches get repeated
- Momentum is lost
- Mission timeline extends unnecessarily

**If your README is precise, complete, and forward-focused:**
- Successor hits the ground running
- All learnings are preserved
- Progress compounds
- Mission continues seamlessly

**You are not writing a report. You are writing a field manual for continuing combat operations.**

Write it with the precision and urgency it deserves.

---

## **FINAL INSTRUCTION**

Update `README.md` now. 

Make it **complete, actionable, and forward-looking only.**

Your successor receives the same mission directive you did. Your README is their situational briefing.

**Execute.**