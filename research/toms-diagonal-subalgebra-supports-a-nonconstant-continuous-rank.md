---
rg: 2
id: toms-diagonal-subalgebra-supports-a-nonconstant-continuous-rank
kind: claim
title: The commutative line subalgebra of Toms's non-simple limit contains a positive element with finite, continuous, non-constant rank
distinct_from:
  toms-schubert-algebra-has-a-non-constant-continuous-rank: that asks for any realizer in the simple algebra B; this asks for a realizer inside one explicit commutative subalgebra of the non-simple limit A, a problem that does not see Toms's twists at all.
  toms-schubert-algebra-continuous-ranks-are-constant: that conjectures constancy of all continuous ranks; its test case for A implies the negation of this claim, and that negation has to be proved without the twists.
  toms-diagonal-quotient-has-nonconstant-continuous-ranks: that realizes ranks on a quotient where all leaf coordinates coincide; this asks for them on a subalgebra, against every trace of A.
---

**OPEN.** Let `A = lim (A_N, phi_N)` be the non-simple limit of Toms's Section 4
(arXiv:2606.12188v2), with `p_1 = theta^d in M_k(A_1)`. Let `P_(1,j)` be the
coordinate lines of `theta^d`, and `P_(N,lambda)` their pushforwards to stage `N`,
`lambda` ranging over `r_N = d_N` indices (leaf and line). Put
`D_N = span { g P_(N,lambda) : g in C(X_N) }` and `D = closure of union D_N`. Then
some `a in D_+` has `tau -> d_tau(a)` continuous and non-constant on `T(A)`.

**Why this subalgebra (proved in the body; elementary).**
- `D_N ≅ C(X_N x [r_N])` and `phi_N(D_N) ⊂ D_(N+1)`, so `D ≅ C(Omega)` with
  `Omega = lim (X_N x [r_N])`. The line-bundle twists enter only through the
  projections `P_(N,lambda)`, which pairwise commute with the centre. So `D`, its
  connecting maps and the restriction map `T(A) -> P(Omega)` are the same for
  Toms's tower and for the untwisted tower (trivial `gamma`).
- In `D`, `b <~ c` iff the open support of `b` lies in that of `c`, and
  `d_tau(a) = nu_tau({a > 0})`. So a realizer is the same as open sets
  `O_(N,lambda) ⊂ X_N` with `O_(N+1,(i,lambda)) ⊇ (copy i)^(-1) O_(N,lambda)`, whose
  counts `#{lambda : x in O_(N,lambda)}` are sandwiched in `[r_N (F_N - eps_N), r_N F_N]`
  with `eps_N -> 0`, where `F_N` is the target read at point traces.
- **Consequence.** If this claim holds, the rigidity conjecture fails for `A`
  in both towers. If it fails, any proof of the conjecture for `A` contains a
  twist-free proof of its failure. So
  `toms-twisted-swap-pairs-are-totally-degeneracy-forcing` alone cannot prove
  the conjecture.

**Model test.**
- *A trivial model satisfies it.* On the diagonal quotient every leaf
  coordinate coincides. The uniformly distributed element of
  `toms-diagonal-quotient-has-nonconstant-continuous-ranks`, rebuilt from the
  leaf blocks `sum_j P_(N,(l,j))` of `p_N` instead of the leaf projections of
  `q_N`, lies in `D`. Its image there realizes non-constant continuous ranks by
  the same computation.
- *The same quotient shows independence of leaves is load-bearing.* Its
  realizer fails in `A` at the adversarial points of that claim's Step 5.

## Attempts

- **Rank counts exist.** `toms-rank-bookkeeping-admits-monotone-realizer-profiles`
  gives counts meeting every rank constraint. What this claim adds is
  **per-line** monotonicity of the open sets.
- **Dead: skew products with digit offsets.** In `omega`-centred coordinates
  `Omega ≅ [r_1] x X_1 x prod_t (X_1^(2^(t-1)) x {0,1} x CP^(j_t))`: own leaf,
  then sibling subtrees and side digits. Every product trace `tau_rho` (leaf
  coordinates i.i.d. `rho`) is a product measure, so
  `U = { s(digits) < h(own leaf) }` has the right measure for them. A point trace
  at stage `m` correlates `h(own leaf)` with the first `m - 1` digits. Every digit
  is correlated at some stage, which is the dead design of
  `toms-schubert-algebra-has-a-non-constant-continuous-rank`.
- **Healing constraint (argument sketched here, unreviewed).** Let `J` lines of
  copy `0` switch on arbitrarily close to `x_0`. At **every** point
  `(x_0, x_1, p)` of the next stage, all but `r_(N+1) eps_(N+1)` of them must
  already be on. Open supports persist nearby, so otherwise the count jumps
  above the band. Large jumps must therefore be healed uniformly in the
  sibling coordinate.
- **Fractional levels are not the obstruction here.**
  `toms-block-diagonal-sharpening-has-fuzz-persistence` concerns traces of
  near projections. A rank counts lines with a positive coefficient, so
  half-filled lines cost nothing. For `D` the only analytic condition is
  `sup_tau nu_tau({0 < a < eps}) -> 0`, i.e. boundaries of `U` are uniformly
  null.
- **Dead: tree-symmetric realizers (argument complete here).**
  - Swapping the two subtrees at a node is an automorphism of `D`. It commutes
    with the connecting maps and preserves the restricted traces.
  - Suppose every `a_m` is invariant under all such swaps. Take a stage-`M` point
    `w` with every leaf at the same `x in X_1`. The swaps fix `w` and act
    transitively on the `K = 2^(M-1)` leaves, so each leaf has the same number of
    lines on. Hence `R_M(w)` is a multiple of `K`, while `r_M = K d`.
  - The sandwich then needs an integer in `[d h(x) - d eps_M, d h(x)]` for every
    `x`. Since `d h(x)` takes every fractional part, `eps_M >= 1/d` for all `M`,
    which contradicts `eps_M -> 0`. So a realizer must break the tree symmetry.
- **Proved: bounded delays align walls.**
  `toms-monotone-block-rounding-obeys-a-miranda-granularity-bound`:
  - per-copy monotonicity plus the slack budget produce an all-wall point once
    `K <= rho/eps_n`, so there `eps_M >= 1/r_n`, and precision cannot decay faster
    than `r^(-(sqrt 5 - 1)/2)`;
  - chains of heals (each heal moves a wall outward by one line) are bounded
    delays, so the healing constraint above cannot be met by them at scale.
  So a realizer must use **macroscopic delays**. At some points a few copies
  sit about `r_n rho/2` lines above their inherited rank. The budget allows at
  most a fraction `4 eps_n/rho` of the copies to do this at once.
- **Open next step.** There are two ways forward.
  - A Poincare–Miranda bound robust to a small fraction of macroscopically
    delayed copies would give `eps_M >= c/r_n` for **all** `M > n`, and so kill
    every realizer in `D`.
  - An asymmetric design that selects its delayed copies continuously, for
    instance by soft ranks of copy averages, would realize a non-constant
    continuous rank in both towers.
