---
rg: 2
id: commutator-root-minus-one-groups-have-generalized-torsion
kind: claim
title: In G(K; -1, 1) = <y, t | y_1^K = [y_0^-1, y_2]> a product of K^2 + K conjugates of y is trivial, so every map keeping y lands in a group with generalized torsion; for the other five commutator-root groups a finite-ball bi-order test finds no such certificate
distinct_from:
  commutator-root-frontier-kills-pl-and-bi-ordered-targets: its item 4 kills bi-orderable targets for (α, β) = (-1, 1) by a convex-jump sign argument; here an explicit positive identity kills every target without generalized torsion (R*-groups), a strictly larger class, and the ball test gives the first evidence for the (1, ±1) cases that it leaves.
  bg-chains-are-residually-tf-solvable-so-g1n-targets-die: that kills Baumslag-Gersten targets by a residual argument on the kernel; this is an order-type obstruction from one identity.
artifacts:
  - experiments/commutator-root-orders-2026-09-18/tower_wp.py
  - experiments/commutator-root-orders-2026-09-18/gt_identity.py
  - experiments/commutator-root-orders-2026-09-18/gt_identity.out
  - experiments/commutator-root-orders-2026-09-18/bo_sat.py
  - experiments/commutator-root-orders-2026-09-18/sat_runs.out
  - experiments/commutator-root-orders-2026-09-18/lowindex.g
  - experiments/commutator-root-orders-2026-09-18/gt_search.py
---

**ESTABLISHED** (written proof, unreviewed) by
[[commutator-root-minus-one-groups-have-generalized-torsion-proof]]. Item 1 is a two-line derivation, checked
exactly for `K ≤ 5` by Britton's lemma. Item 2 is a bounded computation: evidence, not an obstruction.
Nothing is new for the zero-divisor conjecture.

**Setting.** As in [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]]:
`G(K; α, β) = <y, t | y_1^K = [y_0^α, y_2^β]>`, `y_i = t^{-i} y t^i`, `[g, h] = g^{-1} h^{-1} g h`, `N` the normal
closure of `y`. An element `g ≠ 1` is **generalized torsion** if some product of conjugates of `g` is `1`.
Groups without it are the R*-groups. They include all bi-orderable groups, and some that are not
bi-orderable.

## Theorem

1. **Identity.** In `G(K; -1, 1)`, with `K ≥ 1`, put `P_1 = y_0 y_2 y_0^{-1}` and `P_2 = y_3^{-1} y_1 y_3`. Then

   `P_1 · (y_2^K P_2)^{K-1} · y_2^{K-1} · (y_2 P_2 y_2^{-1}) = 1`,

   which is a product of `K^2 + K` conjugates of `y`: 6 for `K = 2`, 12 for `K = 3`.
   - So `y` is generalized torsion.
   - For every `φ: G(K; -1, 1) → Q` with `φ(y) ≠ 1`, the element `φ(y)` is generalized torsion in `Q`. So no
     R*-group receives `y` nontrivially. This covers the 8 words with `(α, β) = (-1, 1)` among the 26.
   - The same word is nontrivial in `G(K; 1, ±1)`, `K ≤ 5` (`gt_identity.out`).
2. **Ball test for a bi-order** (`bo_sat.py`, `sat_runs.out`). Let `B` be the ball of words of length at most `r`
   in `y_0, …, y_{W-1}`, merged by exact equality.
   - One boolean per element of `B` records whether it is positive.
   - The clauses are the necessary conditions for a `t`-invariant bi-order of `N`: exactly one of `g`, `g^{-1}`
     is positive; `g, h > 1 ⇒ gh > 1` when `gh ∈ B`; conjugation by a letter preserves positivity; the index
     shift preserves positivity.
   - Every identity used in a clause is decided exactly by Britton's lemma. Finite quotients only propose the
     candidates.
   - Results:
     - `G(2; -1, 1)` is UNSAT already at `W = 3, r = 3`, which calibrates item 1.
     - `G(2; 1, 1)` is SAT at `W = 4, r = 4` (3020 elements, 2.6·10^5 clauses) and at `W = 5, r = 4` (7858
       elements, 10^6 clauses).
     - `G(2; 1, -1)`, `G(3; 1, 1)` and `G(3; 1, -1)` are SAT at `W = 4, r = 4`.
     - `G(3; -1, 1)` is UNSAT at `W = 4, r = 3`, as item 1 requires.
   - A meet-in-the-middle search (`gt_search.py`) over products of up to 6 conjugates `u^{-1} y_i u` with `|u| ≤ 2`,
     matched in 24 finite quotients and checked exactly, finds no generalized torsion in `G(2; 1, 1)`.

## Where it stops

- Whether `G(2; 1, 1)` is bi-orderable, or even R*, is still open. Item 2 finds no finite certificate up to the
  ball sizes above. By shift invariance, every solution gives all `y_i` the same sign.
- A bi-order must also satisfy the forced strictly increasing chain of convex classes of the frontier node,
  item 4. So `y_{n+1}` is infinitely larger than `y_n`, and the relation reads `y_1^2 ≡ y_2^{-1} y_0 y_2` on each
  convex jump.
- **Next step.** Either push the ball test to `r = 5, 6` (the pair loop is the cost, so it needs a sparser
  product enumeration), or build the order.
  - A route to building it is the HNN structure of `G` over `P = <y_0, y_1, y_2> ≅ π_1(N_3)`, the genus-3
    nonorientable surface group, which is bi-orderable (Rolfsen–Wiest). `t` conjugates `<y_0, y_1>` onto
    `<y_1, y_2>`.
  - What is needed is a family of bi-orders on the iterated amalgams of copies of `P` that the map
    `y_0, y_1 ↦ y_1, y_2` preserves, with the increasing convex chain above.
