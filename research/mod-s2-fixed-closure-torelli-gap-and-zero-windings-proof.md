---
rg: 2
id: mod-s2-fixed-closure-torelli-gap-and-zero-windings-proof
kind: route
title: Pin the mean eigenphase on the determinant grid by compactness of Hom(M, U(n)), add spreads along tensor words, and for a fixed closure kill the commutator part of the identity component and replace the rest by a representation of bounded dimension
target: mod-s2-fixed-closure-torelli-gap-and-zero-windings
requires:
  - deligne-torelli-character-counts-separating-twists
---

Notation as in the target.

**Imports.**
- **[ST5]** from `deligne-torelli-character-counts-separating-twists`, verbatim: "No finite-dimensional unitary
  representation of `M` sends a separating twist to `omega I` or to `omega^2 I`."
- **[H1]** `H_1(Mod(S_2); Z) = Z/10` (Farb–Margalit, *A Primer on Mapping Class Groups*, §5.1). The same fact
  is used in the remark of `mod-s2-separating-twist-character-semigroup-dichotomy` and in
  `mod-s2-near-identity-torelli-windings-vanish` ("`kappa(rho(t_s))` lies in `(1/10)Z`"). Consequence: for
  honest `rho : M -> U(n)`, `det rho(t_s)` lies in `mu_10`, and if `||rho(t_s) - I|| < 2` then
  `kappa(rho(t_s)) in (1/10)Z`, since `exp(2 pi i kappa) = det`.
- **[FG]** `M` is finitely generated (Dehn–Lickorish). Hence `Hom(M, U(n))`, with the topology of pointwise
  convergence on a finite generating set, is compact. Each `rho -> rho(w)`, for a fixed word `w`, is
  continuous, and a pointwise limit of homomorphisms is a homomorphism.
- **[Lie]** Standard compact Lie theory:
  - a closed subgroup of `U(n)` is a compact Lie group with finitely many components;
  - a compact connected Lie group `G` has Lie algebra `g = z + s`, with `z` the centre and `s = [g, g]`
    semisimple and a direct sum of simple ideals. Every automorphism preserves `z` and `s`, and every
    `Ad(G)`-stable subspace of `s` is a sum of simple ideals;
  - `G = (T x S~)/F`, with `T = Z(G)^0` a torus, `S~` compact simply connected semisimple (Weyl), and `F`
    finite central;
  - the connected subgroup with a given semisimple ideal as Lie algebra is closed, being the image of a
    compact simply connected group (Weyl);
  - the image of a torus under a continuous homomorphism is a closed torus.
- **[Gen]** A connected compact group is the union of the increasing open sets `V^k` for any open
  neighbourhood `V = V^(-1)` of `1`, hence equals `V^k` for some finite `k`.
- **[Sub]** If a smooth map of manifolds has surjective differential at one point, its image contains an open
  set (implicit function theorem).
- **[Rep]** Standard representation theory of compact groups:
  - irreducibles of `A x B` are the outer tensor products of irreducibles;
  - Clifford theory for a closed normal subgroup of finite index: the restriction of an irreducible is
    `e` times the sum over one orbit of conjugates;
  - induction from a closed normal subgroup of finite index `r` multiplies dimension by `r`, and its
    restriction is the sum of the `r` conjugates;
  - if `Z` is central of index at most `r` in a compact group `C`, the irreducibles of `C` have dimension at
    most `r`, since `(dim)^2 <= [C : Z]`;
  - every character of a finite central subgroup of a compact group occurs as the central character of some
    irreducible (Peter–Weyl).
- **[Pow]** If `U` is unitary with `||U^k - I|| < sqrt 3` for all `k >= 1`, then `U = I`. If an eigenvalue is
  `exp(i phi)` with `0 < |phi| <= pi`, some power `k` has `k phi` within `[2 pi/3, 4 pi/3]` mod `2 pi`, and then
  `||U^k - I|| >= sqrt 3`.

## Step A: (FC1)

*Spread and mean.* If `s(U) < pi`, the shortest arc `[a, a + s(U)]` containing the spectrum is unique. Lift
the eigenphases to `phi_j in [a, a + s(U)]` and put `mu = (1/n) sum_j phi_j`. Every `phi_j` is within
`s(U)` of `mu`, so `||U - exp(i mu) I|| <= s(U)`. Also `det U = exp(i n mu)`.

*The grid.* For honest `rho` of dimension `n` with `s(rho(t_s)) < pi`, put `c = exp(i mu)`. Then
`c^n = det rho(t_s) in mu_10` by [H1], so `c in mu_(10 n)`, a finite set.

*Proof of (FC1).* Suppose (FC1) fails for some `n`. Then there are honest `rho_k : M -> U(n)` with
`s_k = s(rho_k(t_s)) -> 0` and `c_k notin E_n`. Pass to a subsequence along which:
- `c_k = c` is constant, since `c_k` lies in the finite set `mu_(10 n)`;
- `rho_k -> rho_inf` in `Hom(M, U(n))`, by [FG].

Then `rho_inf(t_s) = lim rho_k(t_s)` and `||rho_k(t_s) - c I|| <= s_k -> 0`, so `rho_inf(t_s) = c I` and
`c in E_n`. This is a contradiction.

*`Ebar_(n0)`.* Each `E_n` lies in `mu_(10 n)`, so `Ebar_(n0)` lies in `mu_L` with `L = 10 lcm(1, ..., n0)` and is
finite. Exact values are closed under products and inverses:
- `rho (x) rho'` realizes `c c'`;
- `conj rho` realizes `c^(-1)`;
- the trivial representation realizes `1`.

So every element of `Ebar_(n0)` is an exact value `sigma(t_s) = c I` of some honest `sigma`, and [ST5] gives
`omega, omega^2 notin Ebar_(n0)`. Hence `delta > 0`.

## Step B: (FC2)

*Spread lemma.* For unitaries `X, Y`:
- `s(X (x) Y) >= max(s(X), s(Y))`, since the spectrum of `X (x) Y` contains a rotated copy of each factor's
  spectrum;
- if `s(X), s(Y) < pi/2`, then `s(X (x) Y) = s(X) + s(Y)`. The product spectrum lies in the sum arc, of length
  `< pi`, and contains both of its endpoints.

By induction along a word `W = A_1 (x) ... (x) A_l` with `s(W) < pi/2`, every partial product has spread
`< pi/2`, and
```text
s(W) = s(A_1) + ... + s(A_l) .
```

*(i) Gap.* Let `W = (+)_alpha W_alpha` be in `R_(n0)` and `lambda in Lambda`. Suppose
`||W(t_s) - lambda I|| <= eps`, and put `theta = 2 arcsin(eps/2)`, the angle `eps` subtends. Suppose further
that `theta < min(delta/3, s0*/2)`.
- Fix a word `W_alpha = A_1 (x) ... (x) A_l`. Its spectrum at `t_s` lies within angle `theta` of `lambda`,
  so `s(W_alpha(t_s)) <= 2 theta < s0* <= pi/2`.
- By the spread lemma, `sum_i s(A_i(t_s)) = s(W_alpha(t_s)) <= 2 theta`, so each `s(A_i(t_s)) < s0(n_i)`.
  Here `A_i` is honest of dimension `n_i <= n0`; a conjugate of an honest representation is honest.
- By (FC1), each eigenvalue of `A_i(t_s)` is within angle `s(A_i(t_s))` of some `c_i in E_(n_i)`, where
  `c_i` is the mean direction of `A_i`.
- An eigenvalue of `W_alpha(t_s)` is a product `prod_i a_i` of eigenvalues, so it is within angle
  `sum_i s(A_i(t_s)) <= 2 theta` of `prod_i c_i in Ebar_(n0)`. It is also within `theta` of `lambda`, so the
  angle from `lambda` to `Ebar_(n0)` is at most `3 theta < delta`.

This contradicts the definition of `delta`. Hence `theta >= min(delta/3, s0*/2)`, which is (FC2 i).

*(ii) Windings.* Let `||W(t_s) - I|| < 2 sin(theta0/2)`, and let `theta < theta0` be the corresponding angle.
Since `kappa` is additive over direct sums, it suffices to show `kappa(W_alpha(t_s)) = 0` for each word
`W_alpha = A_1 (x) ... (x) A_l`.
- As in (i), `s(W_alpha(t_s)) <= 2 theta < pi/2` and `sum_i s(A_i(t_s)) <= 2 theta`.
- Write the eigenphases of `A_i(t_s)` as `mu~_i + t_(i j)` for `j = 1, ..., n_i`. Here `mu~_i` is a real
  lift of the mean phase, `|t_(i j)| <= s(A_i(t_s))` and `sum_j t_(i j) = 0`. By Step A,
  `exp(i mu~_i) = c_i in mu_(10 n_i)`, which lies in `mu_L`. No use of (FC1) is needed here.
- Put `m~ = sum_i mu~_i`. The eigenvalues of `W_alpha(t_s)` are
  `exp(i (m~ + T_J))`, with `T_J = sum_i t_(i j_i)` for multi-indices `J = (j_1, ..., j_l)`, and
  `|T_J| <= 2 theta`.
- Any one eigenvalue is within angle `theta` of `1`, so `exp(i m~) in mu_L` is within angle `3 theta` of `1`.
  Since `3 theta < 2 pi/L`, `exp(i m~) = 1`.
- So the eigenvalues are `exp(i T_J)` with `|T_J| < pi`, and the principal logarithm gives
  ```text
  2 pi kappa(W_alpha(t_s)) = sum_J T_J = sum_i ( prod_(i' != i) n_(i') ) sum_j t_(i j) = 0 .
  ```

This proves (FC2 ii).

## Step C: (FC3), the commutator kill

Let `G = cl rho0(M)`. By [Lie] it is a compact Lie group, `G0 = G^0` has finite index `r`, and `g = rho0(t_s)`
normalizes `G0`. Put `alpha = Ad(g)|G0`, an automorphism of `G0`, and
```text
psi(h) = h alpha(h)^(-1) = h g h^(-1) g^(-1)   (h in G0),        D = psi(G0),   so 1 in D and D lies in G0 .
```

*The ideal.* Let `m` be the span of `Ad(y)(1 - d alpha) g0` over `y in G0`, where `g0 = z + s` is the Lie
algebra of `G0`. Since `d alpha` preserves `z` and `s` and `Ad(y)` fixes `z`,
```text
m = (1 - d alpha) z  (+)  s_I ,
```
where `s_I` is the span of the `Ad(y)(1 - d alpha) s`. This is an `Ad(G0)`-stable subspace of `s`, hence a
sum of simple ideals. Now put
```text
N = (1 - alpha)(T) . S_I ,
```
with the following parts:
- `T = Z(G0)^0`, and `(1 - alpha)(T)` is the image of `t -> t alpha(t)^(-1)`, a closed torus with Lie algebra
  `(1 - d alpha) z`;
- `S_I` is the closed connected subgroup with Lie algebra `s_I`, by [Lie].

`N` is closed, connected and normal in `G0`, with Lie algebra `m`. It is `alpha`-stable, since
`d alpha (Ad(y)(1 - d alpha)X) = Ad(alpha y)(1 - d alpha)(d alpha X)`.

*`D` lies in `N`.* On the connected group `G0/N`, the induced automorphism has differential induced by
`d alpha`, and `d alpha` is congruent to the identity modulo `m`. So it is the identity, and
`psi(h) in N` for all `h`.

*`D` fills `N` in boundedly many steps.* Let `Phi_j(h_1, ..., h_j) = psi(h_1) ... psi(h_j)`, a smooth map
`G0^j -> N`, and put `P_i = psi(h_1) ... psi(h_i)`.
- The right-trivialized differential of `psi` at `h` has image `Ad(h)(1 - d alpha) g0`.
- So the differential of `Phi_j` has image `sum_i Ad(P_(i-1) h_i)(1 - d alpha) g0`.
- Given `h_1, ..., h_(i-1)`, the element `y_i = P_(i-1) h_i` ranges over all of `G0` as `h_i` does. Choose
  `j = dim m` elements `y_i` whose summands span `m`.

At that point the differential is onto `T N`. By [Sub], `Phi_j(G0^j)`, which lies in `D^j`, contains a nonempty
open subset `U` of `N`. Then `V = U U^(-1)` is an open neighbourhood of `1` in `N`, it lies in
`(D u D^(-1))^(2j)`, and `V = V^(-1)`. By [Gen], `N = V^k` for some `k`. With `m0 = 2 j k`, every element of
`N` is a product of at most `m0` elements of `D u D^(-1)`. The integer `m0` depends only on `rho0`.

*Kill.* Let `pi` be a continuous unitary representation of `G` with `||pi(g) - c I|| <= eps` for a unit
scalar `c`. Then `pi(h g h^(-1))` is also within `eps` of `c I`, so
`||pi(psi(h)) - I|| <= 2 eps` on `D`, and `||pi(n) - I|| <= 2 m0 eps` on `N`. If `2 m0 eps < sqrt 3`, then
[Pow] applied to each `pi(n)` (with `n^k in N`) gives `pi(N) = 1`. The kernel of `pi` is normal in `G`, so
`pi` kills the normal closure
```text
N^ = product of the finitely many conjugates x N x^(-1),  x in G/G0 ,
```
a closed connected normal subgroup of `G` contained in `G0`.

## Step C (continued): bounded replacement

Put `G1 = G/N^`, `g1` the image of `g`, and `G1^0 = G0/N^`. Then `psi(G0)` lies in `N`, which lies in `N^`, so
`g1` centralizes `G1^0`. Let `C` be the centralizer of `G1^0` in `G1`. It is closed, normal (as `G1^0` is
normal) and contains `g1`, and `C` meets `G1^0` in `Z(G1^0)`, which is central in `C`. So
`[C : Z(G1^0)] <= [G1 : G1^0] <= r`, and by [Rep] every irreducible `tau` of `C` has `dim tau <= r`.

`L0 = G1^0 C` is a closed normal subgroup of finite index at most `r`, and
```text
L0 = (G1^0 x C) / {(z, z^(-1)) : z in Z(G1^0)} .
```
Its irreducibles are `sigma (x) tau`, with `sigma` irreducible on `G1^0`, `tau` irreducible on `C`, and equal
central characters on `Z(G1^0)`. An element `x` of `C` acts as `1 (x) tau(x)`.

*Bounded twin.* By [Lie], `G1^0 = (T1 x S1~)/F1`. For each character `xi` of the finite group `Z(S1~)`, fix an
irreducible `s_xi` of `S1~` with central character `xi` [Rep], and let `B = max_xi dim s_xi`. Given `sigma`,
its central character on `Z(G1^0) = (T1 x Z(S1~))/F1` pulls back to `chi (x) xi`, trivial on `F1`. Then
`sigma' = chi (x) s_xi` is irreducible on `T1 x S1~` and trivial on `F1`. So it is an irreducible of `G1^0`
with the same central character as `sigma`, and `dim sigma' <= B`.

*(FC3 i).* Let `pi != 0` be continuous with `||pi(g) - lambda I|| = eps`, `lambda in Lambda`. It suffices to
treat one irreducible constituent, which has the same bound. If `2 m0 eps >= sqrt 3`, then
`eps >= sqrt 3/(2 m0)`. Otherwise `pi` factors through `G1`. Pick a constituent `sigma (x) tau` of `pi|L0`.
- For `x in G1`, `x^(-1) g1 x in C` acts on that constituent as `1 (x) tau(x^(-1) g1 x)`, a compression of
  `pi(x^(-1) g1 x)`, which is within `eps` of `lambda I`. So `||tau(x^(-1) g1 x) - lambda I|| <= eps` for all
  `x`.
- Put `pi' = Ind_(L0)^(G1) (sigma' (x) tau)`, of dimension at most `r . B . r = D0`. By [Rep], `pi'|L0` is the
  sum over coset representatives `x` of the conjugates. On these `g1` acts by `1 (x) tau(x^(-1) g1 x)`, so
  `||pi'(g1) - lambda I|| <= eps`.
- `pi' o (G -> G1) o rho0` is an honest representation of `M` of dimension at most `D0` sending `t_s`
  within `eps` of `lambda I`.

By [FG], `rho -> ||rho(t_s) - lambda I||` attains its minimum on the compact `Hom(M, U(n))` for each
`n <= D0`, and the minimum is positive by [ST5]. Call the least of these minima `g_(D0) > 0`. Then
```text
eps  >=  c(rho0) := min( sqrt 3/(2 m0) , g_(D0) ) ,
```
which depends only on `rho0`, through `G`.

*(FC3 ii).* Put `c'(rho0) = min( sqrt 3/(2 m0) , 2 sin(pi/(10 D0)) )`, and let `pi` be continuous with
`||pi(g) - I|| = eps < c'(rho0)`. Since `kappa` is additive over direct sums, take `pi` irreducible. By the
kill, `pi` factors through `G1`.
- *Clifford.* `pi|L0 = e . sum over x in G1/I` of `(sigma (x) tau)^x`, where `I` is the inertia group of
  `sigma (x) tau`. The conjugate by `x` is `sigma^x (x) tau^x`, and `g1` acts on it as
  `1 (x) tau(x^(-1) g1 x)`, within `eps` of the identity. Hence
  ```text
  kappa(pi(g1)) = e . dim sigma . S ,      S = sum over x in G1/I of kappa( tau(x^(-1) g1 x) ) .
  ```
  The summand depends only on the isomorphism class of `tau^x`, so only on the coset `x I`.
- *Twin.* For `pi' = Ind_(L0)^(G1)(sigma' (x) tau)`, the same computation over `G1/L0` gives
  `kappa(pi'(g1)) = dim sigma' . [I : L0] . S`, and `||pi'(g1) - I|| <= eps`.
- *Bounded dimension.* `pi' o rho0` is honest of dimension `n <= D0`, with `||pi'(g1) - I|| <= eps`. Its
  eigenphases satisfy `|phi| <= 2 arcsin(eps/2) < pi/(5 D0)`, so `|kappa| < n/(10 D0) <= 1/10`. By [H1],
  `kappa(pi'(g1)) in (1/10)Z`, so `kappa(pi'(g1)) = 0`.
- Hence `S = 0` and `kappa(pi(g1)) = 0`.

Replacing `c(rho0)` by `min(c(rho0), c'(rho0))` gives (i) and (ii) with one constant.


## Step D: (FC4)

- (a) Along a gap witness, `||rho_k(t_s) - lambda I|| -> 0`. So eventually it is below the constant of
  (FC2 i) for any fixed `n0`. Along a (Z) witness, `||rho_k(t_s) - I|| -> 0` and `kappa != 0`; (FC2 ii)
  excludes this once the distance is below `2 sin(theta0/2)`.
- (b) This is the same argument, with the constant of (FC3) applied to `pi_k o rho0`.

## Step E: (FC5)

In `K = T^2 x| <A>`:
- `det(1 - A) = 3`, so `1 - A` is onto `R^2` and `(1 - A) T^2 = T^2`. Each `t A(t)^(-1)` is a commutator, so
  `T^2` lies in `[K, K]`, and `K/[K, K] = C_3` is finite.
- The irreducibles are:
  - the three characters of `C_3`, which send `g` to `1`;
  - the `Ind chi_v` for nonzero `v in Z^2`. These have dimension 3, because `A` fixes no nonzero vector.

  On `Ind chi_v`, the eigenvalues of `g` are `exp(2 pi i <v, A^k g>)` for `k = 0, 1, 2`. They are never all
  `omega`, since `<v, g> = v_1 sqrt 2 + v_2 sqrt 3` is irrational.
- The map `v -> (<v, g>, <v, A g>)` mod `Z^2` has dense image, by Kronecker's criterion: `(w_1 + w_2 A) g` has
  first coordinate `w_1 sqrt 2 - w_2 sqrt 3`, which is not an integer for `w != 0`. The third phase is then
  forced, since `(1 + A + A^2) g = 0`. So `inf_v ||Ind chi_v (g) - omega I|| = 0`.
  `torus_c3_near_omega.py` finds `0.0021` at `|v|_inf <= 1000`.

The analogue of Step C runs all the way to `D0 = 3`:
- `alpha = id` on `T^2`, so `N` is trivial;
- `C = L0 = T^2`, and `r = 3`.

It fails only at the last line, because the continuous 3-dimensional representations of `K` do not form a
compact set. A limit point of `Ind chi_(v_k)`, restricted to the discrete group generated by `g` and `A`, sends
`g` to `omega I`. That is the analogue of a failure of [ST5]. So (FC3) genuinely uses both [FG] and [ST5].
