---
rg: 2
id: mod-s2-torelli-metaplectic-maslov-line-proof
kind: route
title: Push commutator lifts through the real untwisting, pin its slope with the braid group B_3, and bound the index by Deligne's residual
target: mod-s2-torelli-characters-have-a-metaplectic-maslov-line
requires:
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
  - genus-two-torelli-freely-generated-by-separating-twists
  - deligne-torelli-character-counts-separating-twists
  - mod-s2-real-untwisting-identifies-deligne-norm-parameters
  - deligne-covers-of-sp2g-z-have-finite-residual-2z
  - metaplectic-half-class-has-an-exact-finite-model
---

Notation as in the target. Inputs:
- **[H]** `H_1(M;Z) = Z/10`, and `1 -> K -> M -> Gamma -> 1` is exact.
- **[Mess]** `K` is free on separating twists, one per splitting. Two separating twists with the same splitting are
  conjugate by an element of `K`.
- **[ST1]** The separating twists form one conjugacy class of `M`, and they generate `K`.
- **[U1]** There is `f : M -> R` with `f(m) + f(m') - f(mm') = b(pi m, pi m')`, where `b` is the normalized integral
  cocycle of `Gamma~ = Gamma x_b Z`. Also `f|_K = r F` with `r = f(t_s)`, and `r = a/10` with `a` an integer.
- **[DR]** `z^2` lies in every finite-index subgroup of `Gamma~`. This is the inclusion `2Z <= Res_fin(Gamma~)`
  recorded in `deligne-covers-of-sp2g-z-have-finite-residual-2z`.
- **[MF2]** `E_2` has a finite quotient in which `z` survives
  (`metaplectic-half-class-has-an-exact-finite-model`).
- **[B3] (classical, by citation).** Let `SL_2(R) -> Sp_4(R)` be the block embedding on one symplectic plane. It
  induces an isomorphism on `pi_1`: the block `U(1) -> U(2)`, `u -> diag(u,1)`, has determinant `u`. So it lifts to an
  injection of universal covers carrying the covering generator to `z`. The preimage of `SL_2(Z)` in the universal
  cover of `SL_2(R)` is the braid group `B_3 = <s_1, s_2 | s_1 s_2 s_1 = s_2 s_1 s_2>`, and its covering generator is
  `(s_1 s_2)^(+-6)`. References: Milnor, *Introduction to algebraic K-theory*, Section 10. The graph uses the same fact
  in the SL_2 check of `deligne-congruence-monomial-models-need-growing-defect-proof`. Trust surface: quoted, not
  re-derived.
- **[CSP] (classical, used only in the Reading of the target).** Every finite-index subgroup of `Sp_4(Z)` contains
  some `Gamma(N)` (Bass–Milnor–Serre).

Model: `Gamma~ = {(g, j) : g in Gamma, j in Z}` with `(g,j)(g',j') = (gg', j + j' + b(g,g'))`, and `z = (e,1)`.

## Step 1: the untwisting homomorphism on the fibre product

Let `P = M x_Gamma Gamma~ = {(x, (g,j)) : pi(x) = g}`, which we write as pairs `(x, j)`. Its product is
`(x,j)(x',j') = (xx', j + j' + b(pi x, pi x'))`. Define

```text
mu : P -> R,     mu(x, j) = j + f(x).
```

Then

```text
mu((x,j)(x',j')) = j + j' + b(pi x, pi x') + f(xx') = j + j' + f(x) + f(x'),
```

so `mu` is a homomorphism. Moreover `mu(e, 1) = 1`, so `mu(z) = 1`. For `k in K` the element `(k, 0)` lies in `P`, and
`mu(k, 0) = f(k) = r F(k)` by [U1].

## Step 2: commutator lifts (ML1, first form)

Fix a finite-index `Gamma' <= Gamma`, with `H = pi^-1(Gamma')` and `Gamma~' = {(g,j) : g in Gamma'}`. Put
`N(Gamma') = {n in Z : z^n in [Gamma~', Gamma~']}`, a subgroup of `Z`.

*Claim.* `N(Gamma') = -r F(K cap [H,H])`.

- (containment in N) Let `k = prod_i [x_i, y_i]` with `x_i, y_i in H`. Choose lifts `X_i = (x_i, 0)` and
  `Y_i = (y_i, 0)` in `P`; they lie over `Gamma'`. Then `prod_i [X_i, Y_i] = (k, n)` for some integer `n`. Its image in
  `Gamma~` is `(pi k, n) = (e, n) = z^n`, and it is a product of commutators of elements of `Gamma~'`. So `n` lies in
  `N(Gamma')`. Apply `mu`. A commutator maps to `0`, so `0 = mu(k, n) = mu((k,0)(e,n))`. Here `b(e, .) = 0`, so
  `(k,0)(e,n) = (k,n)` and `mu(k,n) = r F(k) + n`. Hence `n = -r F(k)`.
- (containment in -rF) Let `z^n = prod_i [G_i, G'_i]` with `G_i, G'_i` in `Gamma~'`. Since `pi` is onto, choose
  `x_i, y_i in H` over the `Gamma`-coordinates of `G_i, G'_i`, and put `X_i = (x_i, j_i)` and `Y_i = (y_i, j'_i)`, with
  the `Z`-coordinates of `G_i, G'_i`. Commutators in `P` do not depend on the central coordinates. So
  `prod_i [X_i, Y_i] = (k, n)` with `k = prod_i [x_i, y_i]` in `[H,H]` and `pi(k) = e`. Hence `k` lies in
  `K cap [H,H]`, and as above `n = -r F(k)`.

So `N(Gamma') = m(Gamma') Z`, where `m(Gamma')` is the order of `z` in `H_1(Gamma~')` (with `0` for infinite order),
and

```text
m(Gamma') Z  =  r F(K cap [H,H]).                                       (1)
```

## Step 3: the index divides 2

`Gamma~'` is finitely generated, being of finite index in the finitely generated `Gamma~`. So
`A = H_1(Gamma~'; Z)` is a finitely generated abelian group, hence residually finite. Suppose `2 zbar != 0` in `A`,
where `zbar` is the image of `z`. Then there is a finite quotient `q : A -> Q` with `q(2 zbar) != 0`. Its kernel
pulls back to a finite-index subgroup of `Gamma~'`, hence of `Gamma~`, that does not contain `z^2`, contradicting [DR].
So `2 zbar = 0`, and `m(Gamma')` is `1` or `2`. In particular `m != 0`, and by (1) `r != 0`.

*Character criterion.* If `m = 2`, then `zbar` is a nonzero element of order two in the finitely generated abelian
group `A`, and characters of `A` separate points, so some `chi : A -> T` has `chi(zbar) = -1`. Conversely, a character of
`Gamma~'` with `chi(z) = -1` shows `z notin [Gamma~', Gamma~']`, so `m != 1`. If `E_2` splits over `Gamma'`, the
splitting gives a complement of index two in the preimage of `Gamma'` in `E_2`. Its sign character pulls back to
`Gamma~'` with `chi(z) = -1`.

*Monotonicity.* If `Gamma'' <= Gamma'`, then `[Gamma~'', Gamma~''] <= [Gamma~', Gamma~']`, so `N(Gamma'') <= N(Gamma')`,
that is `m(Gamma'') Z <= m(Gamma') Z`.

*Existence of m = 2.* By [MF2], there is a finite-index normal subgroup `N` of `E_2` with `z notin N`. Then
`N cap <z> = 1`, and `N` maps isomorphically onto a finite-index subgroup `Gamma'_0` of `Gamma`. So `E_2` splits over
`Gamma'_0`, and `m(Gamma'_0) = 2`. By monotonicity, `m = 2` on every finite-index subgroup of `Gamma'_0`, hence on a
cofinal family.

## Step 4: the whole group, and r = +-1/5 (ML0)

*F on K cap [M,M].* By [H], `H_1(M) = Z/10`. A separating twist is `(T_a T_b)^6` for the twists `T_a, T_b` of a chain of
two nonseparating curves in the one-holed torus it bounds. All nonseparating twists are conjugate and generate
`H_1(M)`, so `t_s` maps to `12 = 2 mod 10`. By [ST1], `K` is generated by separating twists, so `k in K` maps to
`2 F(k) mod 10`. Hence `k in [M,M]` iff `5 | F(k)`, and

```text
F(K cap [M,M]) = 5Z                (realized by t_s^5).                    (2)
```

*H_1(Gamma) = Z/2.* `Gamma = M/K`, so `H_1(Gamma) = H_1(M)/(image of K) = (Z/10)/(2Z/10) = Z/2`.

*m(Gamma) = 1.* Suppose `chi : Gamma~ -> T` is a character with `chi(z) = -1`. Then `chi^2` kills `z`, so it factors
through `Gamma`, and `chi^4 = 1` because `H_1(Gamma) = Z/2`. By [B3], `Gamma~` contains `B_3` with `z = (s_1 s_2)^(+-6)`.
In `B_3`, `s_1` and `s_2` are conjugate, by `s_1 s_2`, so `chi(s_1) = chi(s_2) = zeta` with `zeta^4 = 1`. Then
`chi(z) = zeta^(+-12) = 1`, a contradiction. By the character criterion, `m(Gamma) = 1`.

*Slope.* Apply (1) with `Gamma' = Gamma`, so `H = M`, and use (2): `Z = r * 5Z`, hence `|r| = 1/5`. This is (ML0), and
`a = 10 r = +-2` is consistent with `3 not | a` from [U1].

*Mod-three consequence.* In Step 3 of `mod-s2-real-untwisting-deligne-norm-parameters-proof`,
`exp(2 pi i r/3) = phi(t_s) omega^(h(t_s))`, with `phi` a character of `M`. Since `t_s` maps to `2 mod 10`, `phi(t_s)` is
a fifth root of unity. With `r = 1/5` this reads `1/15 = j/5 + h/3 mod 1`. Multiplying by 15 and reducing mod 3 gives
`h(t_s) = -1 mod 3`. With `r = -1/5` it gives `h(t_s) = +1 mod 3`. So `h(t_s) = a mod 3`.

## Step 5: conclusion of (ML1)

Substituting `|r| = 1/5` in (1) gives `F(K cap [H,H]) = 5 m(Gamma') Z`, and `z^n in [Gamma~',Gamma~']` iff
`n = -r F(k)` for some `k in K cap [H,H]`. Steps 3 and 4 give the remaining items of (ML1).

## Step 6: characters on the Maslov line (ML2)

*Orbit coordinates.* `H` acts on `H_1(K) = Z[splittings]` by permuting the Mess basis: by [Mess], conjugating a basis
twist gives a twist whose class is the basis element of the image splitting. Since `[K,K] <= [H,K]`, we get
`K/[H,K] = Z^O`, the coinvariants, and the quotient map is `nu`. Also `[H,K] <= K cap [H,H]`. So the image of `K` in
`H^ab` is `K/(K cap [H,H]) = Z^O / L(H)`. Characters of `H` restricted to `K` are therefore exactly the
`theta in (R/Z)^O` that vanish on `L(H)`. Each extends from the subgroup `K[H,H]/[H,H]` of `H^ab` to all of `H^ab`,
because `R/Z` is divisible, hence injective.

*The line.* The character `k -> alpha F(k) mod 1` vanishes on `K cap [H,H]` iff `alpha * 5m Z <= Z` (by ML1), that is
iff `5m alpha` is an integer. For `5m = 5` the nearest point of `(1/5)Z` to `1/3` is `2/5`, at distance `1/15`. For
`5m = 10` it is `3/10`, at distance `1/30`. The chosen `theta` takes the value `alpha` on every orbit, so
`d(H) <= 1/(15m)`. For `x` running over coset representatives of `M/H`, each `x^-1 t_s x` is a separating twist in `K`.
So `Ind_H^M theta` is diagonal on `t_s`, with every entry `theta(x^-1 t_s x) = alpha`. It is the scalar
`exp(2 pi i alpha) I`, and it has finite image when `theta` is chosen of finite order, which divisibility allows.

## Step 7: central separating twists (ML3)

Let `rho` be as in (ML3), with `U = rho(t_s)` central in `rho(M)`. `U` is unitary and preserves each isotypic
component of `rho`. On an irreducible constituent `rho_1` it acts as a scalar `lambda` (Schur), so
`rho_1(k) = lambda^(F(k))` for `k in K`. Suppose `lambda^10 != 1`.

`G = rho_1(M)` is a finitely generated linear group, hence residually finite (Malcev). Choose a finite quotient
`q : G -> Q` with `q(lambda^10 I) != 1`. Let `N = ker(q o rho_1)`, a finite-index normal subgroup of `M`, and put
`Gamma' = pi(N)` and `H = pi^-1(Gamma') = NK`. Then `q rho_1(H) = q rho_1(K)` is the cyclic group generated by
`u = q(lambda I)`, which is central in `Q`. Fix an embedding `<u> -> R/Z` with `u -> 1/s`, where `s` is the order of `u`.
The composite is a character `theta` of `H` with `theta|_K = (1/s) F`. By Step 6, `5m/s` is an integer, so `s | 10` and
`u^10 = 1`, a contradiction. Hence `lambda^10 = 1` on every constituent, and `U^10 = I`.

Every tenth root of unity `exp(2 pi i j/10)` is at distance at least `2 sin(pi/30)` from `omega^(+-1)`, since
`|j/10 - 1/3|` and `|j/10 - 2/3|` are at least `1/30` mod 1. Sharpness and attainment: by Step 3 there is `Gamma'_0` with
`m = 2`, and Step 6 on `H_0 = pi^-1(Gamma'_0)` with `alpha = j/10` gives `Ind theta` with `t_s -> exp(2 pi i j/10) I`.
For `j = 3` this is at distance exactly `2 sin(pi/30)` from `omega`.

## Step 8: the transfer vector (ML4)

Let `n = [M:H]` and `M = disjoint union of x_i H`. For `k in K`, `k x_i = x_i (x_i^-1 k x_i)` with `x_i^-1 k x_i` in
`K <= H`, because `K` is normal in `M`. So `k` fixes every coset, and the transfer `V : M -> H^ab` satisfies
`V(t_s) = prod_i [x_i^-1 t_s x_i]`. `V` is a homomorphism to an abelian group, so it factors through `H_1(M) = Z/10`.
There `t_s^5` maps to `10 = 0`, so

```text
k_T = prod_i (x_i^-1 t_s x_i)^5  lies in  K cap [H,H],     nu(k_T) = ell_T = 5 sum_i e_(o(x_i^-1 t_s x_i)).
```

`ell_T` has nonnegative entries and `F(ell_T) = 5n > 0`. If `v : H -> R` were positive on every separating twist, then
`v(k_T) = sum_o (ell_T)_o v(t_o) > 0`, but `v` vanishes on `[H,H]`. So no such `v` exists.

## Step 9: reduction and certificate (ML5)

*Compactness.* The characters of `H` form a compact group, the dual of the finitely generated group `H^ab`, and
`theta -> max_o ||theta(t_o) - 1/3||` is continuous. So `d(H)` is attained.

*Reduction.* Let `theta_*` be the Maslov-line character of Step 6, with value `alpha_* = 2/5` if `m = 1` and `3/10` if
`m = 2`. Suppose `theta` has `||theta(t_o) - 1/3|| < 1/(15m)` for all `o`.
- If `m = 1`, put `psi = theta_* - theta`. Then `psi(t_o) = 2/5 - theta(t_o)` lies in `(0, 2/15)`.
- If `m = 2`, put `psi = theta - theta_*`. Then `psi(t_o) = theta(t_o) - 3/10` lies in `(0, 1/15)`.

Conversely, `theta = theta_* -+ psi` recovers such a `theta` from any `psi` with values in `(0, 2/(15m))`. If `psi`
were `v mod 1` for a real character `v` with `v(t_o)` in `(0, 2/(15m))`, Step 8 would be contradicted.

*Certificate.* Let `ell in L(H)` have nonnegative entries and `F(ell) = 5m`, and let `theta` be any character of `H`.
Write `theta(t_o) = 1/3 + e_o` with `|e_o| <= 1/2`. Since `theta` vanishes on `L(H)`,
`sum_o ell_o (1/3 + e_o) = 5m/3 + sum_o ell_o e_o` is an integer. Now `5m/3` is at distance `1/3` from `Z` for
`m = 1, 2`, and `|sum_o ell_o e_o| <= 5m max_o |e_o|`. So `max_o |e_o| >= 1/(15m)`, and with Step 6,
`d(H) = 1/(15m)`. The same computation with `ell_T` gives `d(H) >= 1/(15n)` whenever `3` does not divide `n`.
