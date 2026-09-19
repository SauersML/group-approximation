---
rg: 2
id: bs12-faithful-trace-opnorm-correction-via-uniqueness
kind: route
title: HS-stability supplies a genuine lift with the same trace, and full-lift uniqueness conjugates it onto the near-representation
target: bs12-faithful-trace-opnorm-correction
requires: [bs1n-hs-stable-levit-vigdorovich, bs12-full-lift-uniqueness-in-matrix-ultraproducts]
---

Let `(A_N, B_N)` be as in the target.  Extend the pair to maps
`f_N : BS(1,2) -> U(N)` by the normal form `g = t^(-j) a^m t^k`: set
`f_N(g) = A_N^(-j) B_N^m A_N^k`.  The relation defect tends to `0` in
operator norm, so `f_N` is an asymptotic homomorphism in the normalized HS
metric.  It is also an asymptotic homomorphism in norm, word by word.

**Step 1.**  By `bs1n-hs-stable-levit-vigdorovich` (LV Cor D(3)) there are
homomorphisms `rho_N : BS(1,2) -> U(N)`, in the same dimension, with
`d_HS(f_N(g), rho_N(g)) -> 0` for every `g`.  On indices outside the
subsequence, use the trivial representation; this does not matter along
`omega`.

**Step 2.**  Let `phi : A -> Q_omega` be the unital *-homomorphism induced by
`rho = (rho_N)`.  The class of `f` defines a unital *-homomorphism `psi` on
the group algebra of `G`, because the relations hold exactly in `Q_omega`.
`psi` extends to `A = C*(G)`, since `C*(G)` is universal.  The two maps
agree modulo `J_omega`, because they are HS-close.  Their common image
`theta` in `R^omega` has trace equal to the limit trace, which is faithful
by hypothesis.

**Step 3.**  By `bs12-full-lift-uniqueness-in-matrix-ultraproducts` there is
a unitary `u` in `Q_omega` with `u phi u* = psi` on the generators.  Lift `u`
to unitaries `u_N` in `U(N)`, using polar parts.  Then `(u_N rho_N(t) u_N*,
u_N rho_N(a) u_N*)` are exact pairs, and they are within `o(1)` of
`(A_N, B_N)` in norm along `omega`.

Since `omega` is arbitrary, the conclusion holds along every subsequence,
and hence as `N -> infinity`.  QED.
