---
rg: 2
id: ternary-anti-central-matrix-state-defects-have-a-strict-deficit
kind: claim
title: Over anti-central matrix states on the ternary Leavitt unit group algebra, compressing along a disjoint cylinder defect lowers the two-root defect by a fixed factor
distinct_from:
  ternary-anti-central-disjoint-defects-have-a-strict-deficit: that is the same inequality over anti-central Sylvester rank functions, equivalent to the kill claim; this is the inequality over anti-central matrix states, which have no triangular axiom, and it is equivalent to failure of the rank condition on S_-.
  ternary-anti-central-unit-class-is-nonpositive: that is the counterexample in K_0 form; this is the same statement in deficit form, equivalent to it through two routes, and recorded so that no lane attacks it as a reduction.
  two-root-gate-lower-bounds-hold-for-matrix-states: that is the established transfer of the gap and descent lower bounds to matrix states, whose Consequence paragraph is one direction of the equivalence; this is the open upper-bound inequality that those lower bounds contradict at a minimizer.
artifacts:
  - research/artifacts/matrix-state-deficit-item-two-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x` and `eps_- = 2(1 - [z])`. Let `A_mat` be the set of matrix states `d` on
`F_3[G]` with `d(eps_-) = 1`: normalized, additive on block sums, with `d(XMY) <= d(M)`. There is `theta < 1`
such that for every `d` in `A_mat` and every pair of disjoint nonempty proper cylinders `A`, `B` with proper union:
1. `d(D_A D_B) > 0`;
2. the compressed state `d'(X) = d(F_3[iota_B](X) Q_B D_A)/d(Q_B D_A)` satisfies `d'(D) <= theta d(D)`.

**Restatement, not reduction** (artifact Theorem 2.2). The claim holds iff `A_mat = ∅`, iff `S_-` fails the rank
condition, iff `ternary-anti-central-unit-class-is-nonpositive` holds.
- **Forward.** A minimizer of `d(D)` over `A_mat` violates the claim, so the claim forces `A_mat = ∅` (route
  `matrix-state-deficit-gives-nonpositive-unit-class`).
- **Converse.** With no matrix state the claim holds vacuously (route
  `nonpositive-unit-class-makes-matrix-state-deficit-vacuous`).
- **Restriction.** It implies `ternary-anti-central-disjoint-defects-have-a-strict-deficit` (route
  `matrix-state-strict-deficit-restricts-to-rank-functions`). The converse follows from (U1).

**Violators** (artifact Proposition 3.1). Suppose `S_-` has the rank condition, and let `d_0` be a minimizer.
- `d_0` factors through the largest weakly finite image `W` of `S_-`.
- At every configuration it violates item 1, or it violates item 2 with `d_0'(D) >= d_0(D)`.
- The violation uses only commuting compression, `F_3[iota_B](eps_-) = Q_B`, the two-root criterion, and the
  descent positivity of `two-root-gate-lower-bounds-hold-for-matrix-states` item 3.
- It uses no nilpotency index and no Frobenius step.

## Attempts

- 2026-09-12 `w7-matrix-state-deficit` (artifact `research/artifacts/matrix-state-deficit-item-two-2026-09-12.md`).
  - **(a) Build a violator.** The minimizer above is one whenever `W != 0`. Socle-type states break only the upper
    bound `c_3 <= 2/3`, locally. An example is [SEP] Example 3.3 pulled back to `<x_12(1), x_23(1)>`, which gives
    `d(D) = 1`. Such states are not states on `S_-`, and they do not reach item 2 (Remark 3.2).
  - **(b) Prove it.** A proof amounts to a finite identity `XY = I_n` over `S_-`, with `X` of size `n x (n-1)`
    (Proposition 4.1). That identity is the counterexample itself.
  - **Where it dies.** Every relation of `S_-` holds in `W`. So a proof of item 2 from relations and the state
    axioms also applies at `d_0`, and must prove `W = 0`. No mechanism.
