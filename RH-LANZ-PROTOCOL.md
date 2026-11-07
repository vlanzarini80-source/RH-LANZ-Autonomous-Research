# RH-LANZ Research Integrity Protocol

Version: P0.1
Status: Research governance, not an RH proof.

## Objective
Investigate the Riemann Hypothesis (RH): every nontrivial zero rho of the Riemann zeta function satisfies Re(rho) = 1/2.

## Five research roles
1. RESEARCH: examine international literature, original sources, assumptions and prior results.
2. ANALYSIS: formulate precise mathematical lemmas with explicit hypotheses, quantifiers and proofs or identified gaps.
3. COMPUTATION: perform reproducible exact, symbolic and numerical calculations; actively search for counterexamples.
4. FORMALIZATION: verify mathematical statements in Lean 4, requiring actual compilation and an axiom audit.
5. ADVERSARIAL AUDIT: independently challenge every argument, hidden assumption, circular step and claim of novelty.

These roles are not yet running autonomous agents.

## Evidence categories
- PROVED_MATH: complete mathematical argument, subject to independent scrutiny.
- LEAN_VERIFIED: exact theorem compiled successfully in a pinned Lean environment, with axioms inspected.
- EXACT_COMPUTATION: reproducible exact or symbolic result, with scope documented.
- NUMERICAL_EVIDENCE: finite computational evidence, never proof of a universal claim.
- LITERATURE_REPORTED: attributed result with a verifiable primary source.
- CONJECTURE: unproved mathematical claim.
- FAILED: demonstrated error or counterexample.
- INDETERMINATE: insufficient evidence.

## Mandatory verification
Every candidate must record:
- Unique identifier and date.
- Exact statement and hypotheses.
- Dependencies and possible reliance on RH or an equivalent criterion.
- Original sources and comparison with known literature.
- Proof attempt or reproducible code.
- Software versions, inputs, logs and test results.
- Counterexample searches and negative findings.
- Independent audit and unresolved gaps.
- Final decision: GO, STOP or INDETERMINATE.

## Scientific restrictions
- Never insert the desired conclusion among the assumptions.
- Never claim a theorem was compiled unless the compilation actually ran successfully.
- Never use sorry, admit or new axioms in results declared LEAN_VERIFIED.
- A green CI run proves only that the executed checks passed.
- Separate numerical evidence, symbolic computation, formal verification and mathematical proof.
- Never claim RH has been solved without a complete independently scrutinized proof.
- An AI audit is not peer review.

## Repository governance
- Develop on feature branches, not directly on main.
- No automatic merges, public announcements, releases or DOI updates.
- No paid computation or external services without explicit authorization.
- Never commit secrets or credentials.
- Preserve failed attempts and their explanations.

## P0 checkpoint
This file establishes governance only.
Automated agents, scheduled workflows, executable tests and persistent research records remain to be implemented and independently verified.
