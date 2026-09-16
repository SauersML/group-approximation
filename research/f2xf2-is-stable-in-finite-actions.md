---
rg: 2
id: f2xf2-is-stable-in-finite-actions
kind: claim
title: F2 x F2 is stable in finite actions
distinct_from:
  f2xf2-not-stable-in-finite-actions: that is the negation
  sl3z-is-stable-in-finite-actions: that asks it for the Kazhdan group SL3(Z); this asks it for the Haagerup group F2 x F2, for which some action is known not to be weakly contained in finite actions
  alekseev-thom-stability-finite-actions-boundary: that records the literature boundary for general residually finite groups; this is the named statement for F2 x F2, the test case of Gohla--Thom Remark 3.16
  f2xf2-in-paunescu-class: that asks every action to be sofic; given the established transfer and the failure of property MD, this claim would refute that one
---

**OPEN.** For every sofic approximation of `Γ = F_2 × F_2`, the limit action on the Loeb space is weakly
contained in the family of finite `Γ`-actions (Gohla--Thom Definition 3.7). Gohla--Thom (arXiv:2403.09582v2,
Remark 3.16) name `F_2 × F_2` as a test case.

**Consequence.** This claim would give a free nonsofic action of `F_2 × F_2`
(`f2xf2-nonsofic-action-from-finite-action-stability`), and so refute `f2xf2-in-paunescu-class`. Its negation
follows from that target (`f2xf2-finite-action-instability-from-paunescu-class`).

The property is strictly weaker than flexible P-stability: Gohla--Thom note that `F_2 × Z` is stable in
finite actions but not flexibly stable. Ioana shows `F_m × F_k` is not even weakly very flexibly stable
(arXiv:1909.00282, Theorem D), and that result does not touch this claim.

## Attempts

* **Property MD.** MD implies stability in finite actions (Fournier-Facio--Willett, Remark A.4), but
  `F_2 × F_2` lacks MD (`f2xf2-lacks-kechris-property-md`). Dies.
* **Inheritance theorems.** Artifact §0.2 and R6.
  * Gohla--Thom Theorem 3.9 needs an amenable complement, but in `F_2 × F_2 = F_2 ⋊ F_2` the complement is
    `F_2`. Any splitting with amenable complement reduces to the next item.
  * Theorem 3.11 needs `Γ/Λ` amenable. Any such normal `Λ` contains `N_1 × N_2` with `1 ≠ N_i ⊲ F_2`, so
    `Λ` again contains a product of two nonabelian free groups. Reduction only; stalls.
  * No amalgamation theorem for this property appears in Gohla--Thom, Alekseev--Thom or
    Fournier-Facio--Willett. So the splitting `(F_2 × Z) *_{F_2} (F_2 × Z)` gives nothing, even though
    `F_2 × Z` is stable in finite actions.
* **The covering criterion, Gohla--Thom Lemma 3.8(iii).** This is a sufficient condition: honest actions
  cover the sofic approximation `m`-to-`1`.
  * Case `m = 1`: it is exactly the correction excluded by (⋆) of Ioana [Io19b, Theorem D], as quoted in
    arXiv:2008.00554v2, so it fails for `F_2 × F_2`.
  * General `m`: undecided. Ioana's arXiv:2008.00554 Theorem 1.5 concerns the reverse direction, a sofic
    approximation covering honest actions (artifact R3).
* **A concrete test.** Ioana's sofic approximations `σ̃_p` (arXiv:2008.00554v2 §4) are built for
  `F_m × F_k`, `m ≥ 5`, `k ≥ 3`, and pass to `F_2 × F_2` through finite-index subgroups.
  * On `F_{m−1} × F_k` they extend the honest actions `x ↦ ϕ_p(g) x ρ_p(h)^{-1}`.
  * Whether their limit actions are weakly contained in finite actions is undecided (artifact R4).
  * Ioana's obstructions are Hamming-level, while weak containment asks only for finitely many statistics.
    No argument either way was found.
