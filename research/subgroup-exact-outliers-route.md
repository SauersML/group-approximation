---
rg: 2
id: subgroup-exact-outliers-route
kind: route
title: Integral conjugation preserves levels, the dichotomy realizes its conjugacy branch, and the finite cocycle closes
target: subgroup-exact-outliers-do-not-exist
requires:
  - two-power-sector-conjugator-dichotomy
---

**Step 1 (normal core).**  `Lambda_0 = core(Lambda_1)` is normal of
finite index in `Lambda`, property (T) with a Kazhdan pair
`(F_0, eps_0)` derived from `(F_1, eps_1)` and the index.  The
restriction `sigma_m|_(Lambda_0)` is genuine (restriction of a
genuine representation of `Lambda_1`), and by Margulis superrigidity
plus the congruence subgroup property it factors through a
congruence quotient `Lambda_0 / (Lambda_0 cap Lambda(N_m))`.

**Step 2 (level preservation).**  For `g in Lambda = SL_3(Z)`,
`Ad(g)` maps `Lambda_0 cap Lambda(N)` onto itself (integral
conjugation preserves each principal congruence subgroup, and
`Lambda_0` is normal).  Hence `sigma_m|_(Lambda_0)` and
`sigma_m|_(Lambda_0) compose Ad(g)` have the SAME kernel; both are
direct sums of irreducibles of the same finite quotient `Q_m`, and
their multiplicity vectors agree because the two are related by the
automorphism `Ad(g-bar)` of `Q_m` composed with a permutation of the
dual, while the total module is the same space — more directly:
`w mapsto sigma_m(g) sigma_m(w) sigma_m(g)^(-1)` is an
`eta_m`-approximate equivalence between them with `eta_m -> 0`
(almost-multiplicativity on the finitely many products involved),
and two genuine finite-dimensional representations at distance
`o(1)` in trace character are equivalent for large `m` (characters
are integers against each irreducible block; a vanishing difference
is eventually zero).  So exact unitary equivalences exist.

**Step 3 (rigidity upgrade).**  With exact equivalence available and
`sigma_m(g_i)` an `eta_m`-almost-invariant unit vector of the
coupling bimodule of the two genuine representations (the
construction of the conjugator dichotomy, conjugacy branch), the
Kazhdan estimate produces an exact conjugator `u_i^(m)` with
`|| u_i^(m) - sigma_m(g_i) ||_2 <= 2 eta_m / eps_0` (the invariant
vector near `sigma_m(g_i)` has an invariant polar part near it;
nearness to a unitary makes the polar part unitary after a cut of
vanishing trace, absorbed flexibly).

**Step 4 (the finite cocycle).**  The corrected family
`{u_i^(m)}` satisfies `u_i u_j = c(i,j) u_(ij)` with
`c(i,j) = u_(ij)^(-1) u_i u_j` commuting with the exact
`sigma_m(Lambda_0)` up to `O(eta_m)` and hence, after a second
(T)-projection, lying in the commutant `C_m` of a genuine
representation — a finite `Lambda/Lambda_0`-cocycle with
coefficients in `U(C_m)`.  Averaging over the finite group
(Ostrowski-type vanishing for finite groups acting on the unitary
group of a von Neumann algebra, valid up to the abelianized
obstruction in `H^2(Lambda/Lambda_0, T)`) trivializes it after at
most a finite central extension or restriction to the kernel of the
obstruction — the flexibility allowed by the claim.  The resulting
map `lambda_0 g_i mapsto sigma_m(lambda_0) u_i^(m)` is a genuine
projective representation of `Lambda` within `O(eta_m + eta_m /
eps_0)` of `sigma_m` on a generating set, which is the theorem;
uniformity of constants is inherited from `(Lambda : Lambda_0)` and
`eps_0` alone.
