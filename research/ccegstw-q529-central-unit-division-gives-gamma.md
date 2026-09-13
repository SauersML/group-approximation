---
rg: 2
id: ccegstw-q529-central-unit-division-gives-gamma
kind: claim
title: Approximately central division of the unit gives property Gamma for every factorial tracially complete C*-algebra (CCEGSTW Question 5.29)
refuted_by: [central-unit-division-without-gamma-exists]
distinct_from:
  ccegstw-q15-amenable-factorial-ii1-has-gamma: that asks whether amenability alone gives property Gamma; this asks whether approximately central division of the unit gives it, with no Bauer hypothesis.
  central-halving-trivializes-every-closed-bauer-face-bundle: that uses central halving to trivialize bundles over closed faces, which are Bauer; this asks for the whole of property Gamma on a non-Bauer designated trace set.
---

**The question.** CCEGSTW, arXiv:2310.20594v6 (7 Aug 2026), Question 5.29, verbatim: "Does
Proposition 5.27 hold for all factorial tracially complete C∗-algebras (i.e. without assuming that X
is a Bauer simplex)?"

**Proposition 5.27** (cf. CETW Corollary 3.2), verbatim: "Let (M, X) be a factorial tracially complete
C∗-algebra such that X is a Bauer simplex. Suppose that for any ∥ · ∥2,X-separable subset S ⊆ M and
k ∈ N, there exists pairwise orthogonal projections p1, . . . , pk ∈ Mω ∩ S′ with τ(pi) = 1/k for all
i = 1, . . . , k. Then (M, X) has property Γ."

CCEGSTW add: "It remains open whether the approximately central division of the unit as in
Proposition 5.27 implies property Γ outside the setting of Bauer simplices ([25, Question 3.5])."

**REFUTED (2026-09-13, unreviewed)** by `central-unit-division-without-gamma-exists`.
- **The witness.** The completion of Toms's simple no-Γ AH algebra over its Poulsen trace simplex.
- **Why it works.**
  - Its equal-rank block splittings, with growing block counts, divide the unit centrally for every
    `k` (`block-balanced-towers-have-central-halving`).
  - It lacks uniform Γ (`toms-ah-counterexample-to-uniform-gamma`).
- **Credit.** The examples are Toms's, and the block mechanism is CETW's Proposition 5.10, as
  recorded on the block-balanced node.
- **Conclusion.** The Bauer hypothesis in Proposition 5.27 cannot be dropped.
