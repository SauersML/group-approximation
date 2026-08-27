---
rg: 2
id: lambda-exact-p-divisible-ultra-deep-proof
kind: route
title: Twist by J h^D and count the root-subgroup-nontrivial mass with a uniform coadjoint-orbit bound
target: lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible
requires: []
---

**Step 1 (one exact intertwiner).**  `sigma_1 = rho'|_(C_0)` and
`sigma_2 = rho' o Ad(h)|_(C_0)` are genuine representations of `C_0`
through finite quotients.  `(UD1)` says `H` is `epsilon`-almost invariant
for the representation `X |-> sigma_2(c) X sigma_1(c)^*` of `C_0` on
`(M_d, ||.||_2)`, so property (T) of `C_0` (finite index in `SL_3(Z)`) gives
an invariant `T`, i.e. `T sigma_1(c) = sigma_2(c) T` for all `c in C_0`, with
`||H - T||_2 <= epsilon/kappa_0` and `||T|| <= 1` (`T` is the finite-group
average of `H`).

**Step 2 (depth k).**  `C^((k)) = cap_(0<=i<=k) h^-i C h^i` satisfies
`h^i C^((k)) h^-i subset C_0` for `0 <= i < k`, so
`T^k rho'(c) = rho'(h^k c h^-k) T^k` for `c in C^((k))`.  Put
`J = ` the signed permutation matrix of `(1 3)` in `SL_3(Z)`, so
`J h J^-1 = h^-1`, and `g_k = J h^k`.  Then `g_k C^((k)) g_k^-1 = C^((k))`,
`T' := rho'(J) T^k` intertwines `rho'|_(C^((k)))` with
`rho' o Ad(g_k)|_(C^((k)))`, and `||rho'(J) H^k - T'||_2 = ||H^k - T^k||_2 <= k epsilon/kappa_0`.
As in Step 4 of `homogeneous-quotient-deep-tower-proof`, a contraction
intertwiner within `delta` of a unitary forces the isotypic weight measures
`w_1` of `rho'|_(C^((k)))` and `w_2 = iota_* w_1` of the twist (`iota` the
bijection `sigma |-> sigma o Ad(g_k)^-1` of the dual of `C^((k))`) to satisfy
`TV(w_1, w_2) <= 4 delta <= 4 k epsilon / kappa_0`.  (With the defect measured
as in `(UD1)` the constant is at most `12 k epsilon/kappa_0`.)

**Step 3 (levels).**  By the Chinese remainder theorem `rho'` factors through
`SL_3(Z/p^D) x SL_3(Z/m')` and every irreducible constituent is
`pi' = pi'_p (x) pi'_(m')`.  Call `a >= 0` the level of `pi'_p` (least `a`
with `pi'_p` trivial on `Gamma(p^a)`), and let `nu_a` be the total weight of
constituents of level `a`, so `nu_0 + nu_1 + ... + nu_D = 1`.  For `a >= 2`,
`pi'_p` is nontrivial on `N_a = Gamma(p^(a-1))/Gamma(p^a) = sl_3(F_p)`, and by
Clifford theory `pi'_p|_(N_a)` is a multiple of the sum of the characters in
one `SL_3(F_p)`-orbit of a nonzero `Y in pgl_3(F_p)` (characters of
`sl_3(F_p)` are `X |-> exp(2 pi i tr(YX)/p)`).  The element
`u_a = e_12(p^(a-1) m')` acts on `pi'` as `pi'_p(e_12(p^(a-1))) (x) 1`, and a
character `Y` is trivial on it iff `Y_21 = 0`.

**Step 4 (uniform orbit bound).**  The `(2,1)` entry of `g Y g^-1` is
`w^T Y v` with `w^T = e_2^T g`, `v = g^-1 e_1`, and as `g` ranges over
`SL_3(F_p)` the pair `(w, v)` ranges uniformly over `{w != 0, v != 0, w^T v = 0}`
(transitivity of `SL_3(F_p)` on nonzero `v` and of `Stab(v)` on nonzero
`w perp v`).  For fixed `v`, `w^T Y v = 0` holds for all `w perp v` if `v` is
an eigenvector of `Y`, and otherwise for a `1/(p+1)` fraction of them.  A
non-scalar `Y` has at most `p^2 + p - 2` eigenvectors among the `p^3 - 1`
nonzero vectors.  Hence the fraction of the orbit lying on `Y_21 = 0` is at
most `(p^2 + p - 2)/(p^3 - 1) + 1/(p+1) = 1 - c_p`, and the normalized
dimension of the `u_a`-fixed subspace of `pi'` is at most `1 - c_p`.  A
constituent of `pi'|_(C^((k)))` that is trivial on `u_a in C^((k))` lies in
that fixed subspace, so constituents nontrivial on `u_a` carry weight at
least `c_p nu_a` in total over the level-`a` part.

At level `a=1`, the quotient is `SL_3(F_p)`, not the additive Lie layer.
Use instead the conjugate root subgroups `U_12,U_23,U_31`.  They generate
`SL_3(F_p)`, so their common fixed space in a nontrivial irreducible is
zero.  Their fixed-space codimensions are equal, and subadditivity of
codimension makes each normalized codimension at least `1/3`.  Thus level
one contributes at least `(1/3)nu_1` of mass nontrivial on `u_1`.  Put
`b_p=min(c_p,1/3)`; every positive level contributes at least `b_p nu_a`.

**Step 5 (the twisted mass is absent).**  `Ad(g_k)(e_12(x)) = J e_12(p^k x) J^-1 = e_32(+-p^k x)`,
so if `sigma` is nontrivial on `u_a` then `sigma^iota = sigma o Ad(g_k)^-1`
is nontrivial on `e_32(+-p^(a-1+k) m')`.  Take `k = D`: for `a >= 1` this
element lies in `Gamma(p^D m') = Gamma(N)`, on which all of `rho'` is trivial,
so `sigma^iota` is not a constituent of `rho'|_(C^((D)))` and
`w_1(sigma^iota) = 0` while `w_2(sigma^iota) = w_1(sigma)`.  Since `iota` is a
bijection, summing over all such `sigma` gives
`TV(w_1, w_2) >= sum_(a>=1) b_p nu_a = b_p (1 - nu_0)`.  With Step 2 at
`k = D` this is `(UD2)`.
