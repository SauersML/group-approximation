---
rg: 2
id: atiyah-cycle-machinery-transcribes-to-three-variables
kind: claim
title: The operator side of the two-variable Atiyah base change - Lemmas J and L, the pencil reduction, Proposition C with Corollary 6, and continuity on the Noether normalization - holds in three variables
distinct_from:
  atiyah-algebraic-jumps-lie-in-a-proper-zariski-closed-set: that is Lemmas J and L in two variables; this asks for them, with the rest of the operator side, in three variables.
  determinant-conjecture-bounds-determinants-over-galois-orbits: that is Proposition C and Corollary 6 for two-variable pencils; this asks for the three-variable versions together with the reduction and continuity steps.
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part1.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part2.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part4.md
---

**OPEN (not written out).**

Let `G` be torsion-free and satisfy Strong Atiyah over `Qbar` and Lueck's
determinant conjecture. Put `D = D_(Qbar[G])`. The claim is the conjunction of
four statements.

1. **Lemmas J and L.** For every matrix `A` over `Qbar[G][x_1, x_2, x_3]` of
   rank `r` over `D(x_1)(x_2)(x_3)`:
   - the algebraic points where `dim_G ker A` differs from `n - r` lie in a
     proper closed set over `Q`;
   - `dim_G ker A(w) >= n - r` for every `w in C^3`.
2. **Reduction.** Excess at a point with algebraically independent coordinates
   gives a full pencil `M_0 + sum_(i<=3) x_i M_i` over `Z[G]` with
   `kappa_0 >= 1` there, off that closed set.
3. **Proposition C and Corollary 6.** At such a point, every integral product
   `F` of linear forms at affine points of `A^3` satisfies
   `kappa_0 a(F) + (N - kappa_0) b(F) + C deg F >= 0`. Here
   `a(F) = log M(v -> F(S_theta v))` for a fixed parametrization `S_theta` of
   the hyperplane through `theta~ = (1, z)`.
4. **Part 4, Section 7, on threefolds.**
   - Noether normalization onto `A^3`, finite étale off `V(g)`.
   - Fibre sums equal the generic value off `Y`: at algebraic points, at
     points of transcendence degree 1 or 2 (by
     `atiyah-base-change-in-transcendence-degree-two-under-det`), and at
     generic points.
   - Continuity from upper semicontinuity, and constancy from density plus
     connectedness.

## Attempts

* **What the predecessor lane says (not a proof).**
  - Part 3, Section 6: "The Part 2 machinery works in `A^s` verbatim."
  - The route `full-atiyah-base-change-via-cycle-approximation`: "The
    `s`-variable versions of Parts 1-2 are routine transcriptions and not yet
    written out."
  - The Galois-orbit node: "The same proof works in any number of variables."
  - The two-variable versions are reviewed: Theorem 5 (Parts 1-3) PASS in
    `ex-review2-quantum-l2` part 5, and Theorem 6 (Part 4) PASS in part 9.
* **Where a transcription could go wrong** (checklist for the lane that writes
  it):
  - **Lemma J.** Normal form over `D(x_1, x_2)[x_3]` with constant-term
    evaluation in iterated Laurent series. The finitely many bad central roots
    must become a proper closed subset of `A^2`, by the coordinate trick.
  - **(RES2).** Use `Lambda_k = span {zeta^alpha : |alpha| <= k}` with three
    multiplication maps. The unit-valued norm form now has 4 variables, over
    `F_(q^4)`.
  - **Proposition S.** It needs `||S_theta^T (1, zeta)|| >= c ||zeta - z||` for
    a `4 x 3` parametrization.
  - **Part 4.** Upper semicontinuity and connectedness of the étale locus of a
    finite map from a threefold. The intermediate transcendence degrees are
    handled by induction.
* **Not attempted.** The lane ex3-atiyah-td3-philippon stopped at the
  2026-09-13 wrap-up order, after landing the Diophantine input
  `points-of-c3-approximable-by-zero-cycles`.
