---
rg: 2
id: iwahori-bounded-dimensional-vertex-constituents-proof
kind: route
title: Pass to the tracial ultraproduct, split the restricted character by Peterson--Thom, and compare the Gamma(N)-fixed projection on the bounded-dimensional corner with the congruence type I summand
target: iwahori-bounded-dimensional-vertex-constituents-are-congruence
requires:
  - peterson-thom-sl2-s-integer-character-rigidity
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
---

Notation of the target. `A = SL_2(Z[1/2])`, `C = SL_2(Z)`, `Gamma(N)` is the
principal congruence subgroup of level `N` in `C`, and `tr` is the
normalized trace. Characters are normalized, positive definite and
conjugation invariant functions. Extremal characters are the extreme points
of the compact convex metrizable set `Ch(G)` (pointwise topology).

**Standard facts used (not graph nodes).**
* **(F1) Choquet.** In a metrizable compact convex set every point is the
  barycenter of a probability measure on the extreme points, which form a
  `G_delta`.
* **(F2) Factor characters.** A character is extremal iff its GNS von
  Neumann algebra is a factor. Two extremal characters with quasi-equivalent
  GNS representations are equal, by uniqueness of the normal tracial state
  on a finite factor.
* **(F3) Disjoint sums.** For pairwise disjoint representations `theta_i`,
  the central projections onto the summands lie in `(⊕ theta_i)(G)''`, so
  `(⊕ theta_i)(G)'' = ⊕ theta_i(G)''`. Hence, for pairwise distinct
  extremal characters `f_i` and weights `w_i > 0` with sum `1`, the GNS
  algebra of `sum w_i f_i` is `⊕ M_(f_i)` with trace `sum w_i tau_i`.
* **(F4) Amitsur--Levitzki.** The standard polynomial `s_(2D)` vanishes on
  `M_k(B)` for every commutative `B` and every `k <= D`. It does not vanish
  on `M_(D+1)`, so it does not vanish on any II_1 factor, which contains
  `M_(D+1)` unitally.

**Fixed projections.** For a group `H` of unitaries in a von Neumann algebra
`R`, put `Fix(H) = inf_(u in H) ker(u - 1)`, the infimum of kernel
projections. It lies in `W*(H)`. It is preserved by normal
`*`-isomorphisms and by cutting with central projections, and it is the
same in any von Neumann algebra containing `H`. For `H` countable in
`M_k(L^infty(X))` it is computed pointwise almost everywhere.

**Step 1 (ultraproduct and amalgam).** Suppose (BDC1) fails for the `+`
vertex. Then there are `D`, `eta`, `delta > 0` and an infinite set `I` of
indices with `m_n := m(pi_(n,+); D, eta) >= delta` for `n in I`. Fix a
free ultrafilter `omega` containing `I` and put
`M = prod_omega M_(d_n)`, with trace `tau`. The exact representations give
homomorphisms `Pi_± = [pi_(n,±)] : C -> U(M)`. For `s in S_+` the defect
tends to `0`, so `Pi_+(s) = Pi_-(sigma s)`; since `S_+` generates `B_+` and
both sides are homomorphisms, `Pi_+ = Pi_- o sigma` on `B_+`. By the
universal property of `C_+ *_(B_+ = sigma B_-) C_-`, which is `A` by
Serre's tree decomposition (the identification used throughout this lane,
with `C_+ = C` and `g in C_-` mapped to `t^(-1) g t`), there is a
homomorphism `Pi : A -> U(M)` with `Pi|_C = Pi_+`. Put `psi = tau o Pi`,
a character of `A`, and `N_+ = Pi_+(C)''`, whose trace `chi_+ = psi|_C` is
the pointwise `omega`-limit of `tr o pi_(n,+)`.

For the `-` vertex use instead `Pi' = Pi o Ad(t^(-1))`. The map
`Ad(t^(-1)) : [[a,b],[c,d]] -> [[a,b/2],[2c,d]]` is an automorphism of `A`,
and `Pi'|_C = Pi_-`. Everything below uses only that the vertex
representation is the restriction to `C` of a homomorphism of `A` into
`U(M)`, so the `-` case is identical.

**Step 2 (the restricted character).** By (F1) write `psi` as the
barycenter of a probability measure `m` on the extremal characters of `A`.
By `peterson-thom-sl2-s-integer-character-rigidity` each extremal `phi`
either factors through a finite quotient or vanishes off `{±1}`. Let
`E_fin` be the first set and `E_0` the rest.
* `E_fin` is countable. Such a `phi` is the normalized character of an
  irreducible finite-dimensional unitary representation `V` of `A`. By
  (FDU1) of `finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence`,
  `V` factors through `SL_2(Z/q)` for some odd `q`, and there are countably
  many such `V`. Moreover `V|_C` factors through reduction
  `C -> SL_2(Z/q)`. So `phi|_C` is a finite convex combination of normalized
  characters `chi_kappa` of **congruence** irreducibles `kappa` of `C`.
* `psi_0 = integral_(E_0) phi dm` vanishes off `{±1}`, and `psi_0(-1)` is
  real with `|psi_0(-1)| <= m(E_0)`. With `phi_±(g) = 1_(g=1) ± 1_(g=-1)`
  and `b_± = (m(E_0) ± psi_0(-1))/2 >= 0`, we get
  `psi_0|_C = b_+ phi_+ + b_- phi_-`.

Evaluation at a group element is continuous and linear, so
`chi_+ = sum_kappa w_kappa chi_kappa + b_+ phi_+ + b_- phi_-`, a countable
convex combination over distinct congruence irreducibles `kappa`.

The FC-centre of `C` is `{±1}` because `PSL_2(Z)` is ICC. So
`Z(L(C)) = span{1, lambda(-1)}`, and `L(C) p_±` with
`p_± = (1 ± lambda(-1))/2` are II_1 factors with traces `phi_±`. So `phi_±`
are extremal of type II_1, and the `chi_kappa` are extremal of type I.
All are pairwise distinct. By (F3),

```text
N_+ = ⊕_kappa M_(dim kappa)  ⊕  W,                              (P1)
W   = the sum of those L(C)p_± with b_± > 0, a type II_1 algebra.
```

Write `z_kappa` for the central unit of the block `kappa` and `z_II` for the
unit of `W`. In block `kappa` the element `Fix(Pi_+(Gamma(N)))` is the
`kappa(Gamma(N))`-fixed projection. `Gamma(N)` is normal and `kappa` is
irreducible, so that projection is `1` if `kappa` factors through level
`N`, and `0` otherwise. Put `F_N = Fix(Pi_+(Gamma(N)))` and
`N_j = prod_(odd p <= j) p^j`. Every odd level divides `N_j` for large `j`.
Hence

```text
F_(N_j) z_kappa = z_kappa   for j >= j(kappa).                   (P2)
```

(Here `N_+` with the faithful trace `tau` is the GNS algebra of `chi_+`, and
the sum runs over the `kappa` with `w_kappa > 0`.)

**Step 3 (the bounded-dimensional corner).** Let `Q_n <= pi_(n,+)` be the
sum of the constituents counted by `m_n`, with projection `P_n`, so
`tr P_n = m_n` and `P_n` commutes with `pi_(n,+)(C)`. Put `P = [P_n]`, so
`P in N_+'` and `tau(P) = m := lim_omega m_n >= delta`.

*Structure.* `Q_n(C)''` is a sum over constituent classes `j` of blocks
`M_(k_j)` with `k_j <= D`, that is `B_n = ⊕_(k <= D) M_k ⊗ l^infty(J_(n,k))`,
with trace `tr_k ⊗ (weights)`. Choose a matrix representative
`rho_(n,j) : C -> U(k_j)` of each class. Finite sums and fixed matrix sizes
commute with ultraproducts, so `prod_omega B_n = ⊕_k M_k(prod_omega
l^infty(J_(n,k)))`, which sits trace-preservingly in `PMP`. Let `A_k` be the
von Neumann algebra generated by the countably many entries of the block-`k`
components of `Q_omega(g) = Pi_+(g) P`, for `g in C`. It is separable and
abelian with a faithful normal trace, so `A_k = L^infty(X_k, nu_k)` for a
standard finite measure space, with `sum_k nu_k(X_k) = 1` after normalizing
the trace by `m`. Thus `Q_omega` is a measurable field `x -> rho_x` of
`k`-dimensional unitary representations of `C`, defined almost everywhere
(`C` is countable).

*Constituents persist.* Extend `dist_cong` to all tuples in `U(k)^(S_C)` by
the same formula. It is `1`-Lipschitz for `max_s ||.||_op` and conjugation
invariant, so `f(u) = max(0, eta - dist_cong(u))` is continuous on the
compact set `U(k)^(S_C)`. It is a uniform limit of polynomials in the
entries and their conjugates. Each `rho_(n,j)` has `f = 0`, and the
ultraproduct map is a `*`-homomorphism, so `f(rho_x) = 0` almost
everywhere, that is `dist_cong(rho_x) >= eta`. If
`rho_x = ⊕_i sigma_i` is a decomposition into irreducibles, then
`dist_cong(rho_x) <= max_i dist_cong(sigma_i)`, since a direct sum of
congruence representations of levels `N_i` is congruence of level
`lcm N_i`, and the operator norm of a block diagonal matrix is the maximum
of the blocks. So some `sigma_i` has `dist_cong(sigma_i) >= eta`; in
particular `sigma_i` is **not** congruence. For every `N`, the fixed space
of `sigma_i(Gamma(N))` is `sigma_i(C)`-invariant (normality), so it is zero
by irreducibility, since otherwise `sigma_i` factors through
`C/Gamma(N) = SL_2(Z/N)`. Hence, almost everywhere and for every `N`,

```text
dim rho_x^(Gamma(N)) / dim rho_x  <=  1 - 1/dim rho_x  <=  1 - 1/D.   (P3)
```

*The corner avoids W.* The map `y -> yP` on `N_+` is a normal
`*`-homomorphism, since `P in N_+'`. Its kernel is `N_+(1 - z_P)` for a
central projection `z_P`, with `P = z_P P`, and `N_+ z_P` is isomorphic to
`N_+ P`, a subalgebra of `⊕_(k<=D) M_k(A_k)`. By (F4) `s_(2D)` vanishes on
`N_+ z_P`. If `z_P z_II != 0`, then `N_+ z_P z_II` is a nonzero central
summand of `W`, which is a sum of at most two II_1 factors. So it contains a
II_1 factor on which `s_(2D)` vanishes, contradicting (F4). Hence

```text
z_P z_II = 0.                                                   (P4)
```

**Step 4 (two computations of one trace).** Let `E : M -> N_+` be the
trace-preserving conditional expectation, and `h = E(P)`. Since
`uPu^* = P` for `u in Pi_+(C)`, `h` lies in `Z(N_+)`. Also `0 <= h <= 1`,
`tau(h) = m`, and `h = E(z_P P) = z_P h`, so `h z_II = 0` by (P4). As
`F_N in N_+`,

```text
tau(P F_N) = tau(h F_N).                                        (P5)
```

*Congruence side.* By (P1), (P2) and `h z_II = 0`,
`tau(h F_(N_j)) = sum_kappa tau(h z_kappa F_(N_j)) -> sum_kappa tau(h
z_kappa) = tau(h) = m`, by dominated convergence over the countable sum.

*Bounded side.* `P F_N` is the element `Fix` of `Q_omega(Gamma(N))`
computed in `N_+ P`. Cutting by `z_P` and the isomorphism
`N_+ z_P -> N_+ P` preserve `Fix`, and it can be computed in
`⊕_k M_k(A_k)`, where it is pointwise. By (P3),

```text
tau(P F_N) = m * sum_k integral_(X_k) dim rho_x^(Gamma(N)) / k  d nu_k(x)
           <= m (1 - 1/D)          for every N.
```

With (P5) and the congruence side this gives `m <= m(1 - 1/D)`, so `m = 0`.
That contradicts `m >= delta > 0`. This proves (BDC1) for the `+` vertex,
and by Step 1 for the `-` vertex.

**Step 5 (diagonal form).** For each `j` choose `n_j` increasing with
`m(pi_(n,+); j, 1/j) <= 1/j` for all `n >= n_j`, by (BDC1). Put
`D_n = max{ j : n_j <= n }`, and `D_n = 1` if there is no such `j`. Then
`D_n -> infinity` and `m(pi_(n,+); D_n, 1/D_n) <= 1/D_n`. The case
`D_n = 1` is trivial, because `m <= 1`.

**Where the argument uses what.**
* The Peterson--Thom import is used only in Step 2. It is the only
  input that sees the second vertex.
* The odd-congruence dual is used only to identify the finite-quotient
  atoms as congruence.
* Bounded dimension is used twice: in (P3), the weight `1/D` of a
  non-congruence constituent, and in (P4), the polynomial identity that
  separates the corner from the II_1 summand. For growing dimension both
  fail. The weight `1/dim` tends to `0`, and a II_1 factor is a limit of
  matrix algebras, so no identity separates them. This is the blind spot
  described in the target.
