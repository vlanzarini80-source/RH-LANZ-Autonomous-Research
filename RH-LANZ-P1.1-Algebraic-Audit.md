# RH-LANZ P1.1 — Algebraic Audit

Date: 2026-11-08
Source: RH-LANZ Computation Agent report
Status: ALGEBRAICALLY VERIFIED / ANALYTICALLY INDETERMINATE
RH proof: NOT ESTABLISHED

## 1. Objective

Audit the dominant term in the proposed Deshouillers–Iwaniec–Conrey specialization, without assuming an analytic power saving.

## 2. Algebraic calculations

Assume R > 1 and consider the expressions:

T1(R) = R^2
T2(R) = R^(31/16)

Then exactly:

T2(R)/T1(R) = R^(-1/16) -> 0 as R -> infinity.

Therefore T1 dominates T2 for these expressions.

## 3. Impossibility of improving T1 itself

For every delta > 0:

R^2 is not O(R^(2-delta)) as R -> infinity.

Proof: If R^2 <= C R^(2-delta) for all sufficiently large R, then R^delta <= C, which is impossible as R -> infinity.

This establishes a fact about the explicit function T1, not the original oscillatory sum.

## 4. Exact finite checks

For R = 2^(16k), k = 1,2,3,4:

T1 = 2^(32k)
T2 = 2^(31k)
T2/T1 = 2^(-k).

Ratios: 1/2, 1/4, 1/8, 1/16.

These values follow exactly by exponent arithmetic. They are not independent numerical certification of an analytic estimate.

## 5. Scientific distinction

An upper bound involving R^2 does not prove that the original sum S(R) has size R^2.

The possible estimate

|S(R)| <= C R^(2-delta)

for delta > 0 remains a research question and is NOT established.

## 6. Unresolved source checks

- Retrieve the original Deshouillers–Iwaniec Lemma 1.
- Verify all hypotheses and parameter constraints.
- Map the parameters to Conrey Lemma 9.
- Verify the specialization A=N=R^(1/4), U=V=R.
- Derive the dominant term from the original proof.
- Examine the actual Vaughan coefficients and cancellation properties.
- Attempt to falsify any proposed power-saving estimate.

No source-page or formula verification is claimed in this checkpoint.

## 7. Results classification

- Algebraic identities: VERIFIED BY DIRECT REASONING.
- Finite examples: EXACT CONSEQUENCES OF EXPONENT RULES.
- Independent computational execution for this report: NOT DOCUMENTED.
- Applicability of original analytic lemma: UNVERIFIED.
- Power saving for original oscillatory sum: NOT PROVED.
- Improvement beyond 4/7: NOT PROVED.
- Riemann Hypothesis: OPEN.

## 8. Decision

ALGEBRAIC AUDIT: COMPLETE.
ANALYTIC SOURCE AUDIT: INDETERMINATE.

Next checkpoint P1.2: inspect original primary sources before proposing any analytic improvement.
