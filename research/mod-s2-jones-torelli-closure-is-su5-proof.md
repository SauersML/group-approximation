---
rg: 2
id: mod-s2-jones-torelli-closure-is-su5-proof
kind: route
title: Take the torus closure of one Dehn twist to get the B-orthogonal cap projections into the Lie algebra, bracket them to su(5) by an exact minor computation, and read everything else off simplicity of SU(5) and Clifford theory for characters of H/S
target: mod-s2-jones-torelli-closure-is-su5
requires:
  - mod-s2-jones-rectangular-separating-twist-spectrum
  - mod-s2-near-scalar-torelli-closure-dichotomy
  - deligne-torelli-character-counts-separating-twists
artifacts:
  - experiments/jones-torelli-closure-2026-09-19/jones_lie_rank.py
---

Notation as in the target. Standard inputs:
- **(LG)** A closed subgroup of `U(n)` is a Lie group whose Lie algebra is `{X : exp(tX) in G for all t}`.
  The connected closed subgroup with Lie algebra `su(n)` is `SU(n)`.
- **(PW)** Peter-Weyl and Frobenius reciprocity for compact groups.
- **(N)** Niven's theorem: if `theta/pi` and `cos theta` are both rational, then
  `cos theta in {0, +-1/2, +-1}`.

## Step 0: the cap operators are B-orthogonal projections up to scale

Each `g_i = A + A^(-1) e_i` is `B`-unitary, by (J1) of `mod-s2-jones-rectangular-separating-twist-spectrum`,
and `e_i = A (g_i - A)` is a polynomial in `g_i`. So `e_i` is `B`-normal. From `e_i^2 = delta e_i` (checked
exactly in the artifact) its eigenvalues lie in `{0, delta}`, which are real. So `e_i` is
`B`-self-adjoint, and `P_i = e_i / delta` is the `B`-orthogonal projection onto `im e_i`.

The rank of `e_i` is 2: its image is spanned by the two matchings containing the cap `(i, i+1)`. On
`im e_i` the operator `g_i` acts by `A + delta/A = -A^(-3)`, and on `ker e_i` by `A`. So
```text
rho(s_i) = beta A (I - P_i) + beta (-A^(-3)) P_i ,     ratio  -A^(-4) = -exp(-4 i x) .
```

## Step 1: i(P_i + r I) lies in Lie(G)

Fix `i` and let `T` be the closure of `{rho(s_i)^n}`. It lies in the 2-torus
`{u (I - P_i) + v P_i : |u| = |v| = 1}`. Consider the continuous homomorphism `q(u, v) = v/u`. It maps
`rho(s_i)^n` to `(-e^(-4ix))^n`. This has infinite order, because `x/pi` is irrational, so these powers are
dense in the circle. `q(T)` is compact and contains them, so `q(T)` is the whole circle.

`T` has finitely many components, so `q(T^0)` has finite index in the circle, and it is connected; so it is
the whole circle. Therefore `T^0` is a nontrivial torus not contained in the scalars. Its Lie algebra
contains some `i(p (I - P_i) + q' P_i)` with `p, q'` real and `p != q'`. Rescaling, `i(P_i + r_i I)` lies in
`Lie(G)` for some real `r_i`, by (LG).

## Step 2: Lie(G) contains su(V,B)

Brackets of the elements of Step 1 kill the scalars:
```text
[i(P_j + r_j I), i(P_k + r_k I)] = - [P_j, P_k] ,
```
and iterating, `Lie(G)` contains `i^m [P_(j_1), [P_(j_2), ..., [P_(j_(m-1)), P_(j_m)]]]` for every `m >= 2`.
Since `delta` is real and nonzero, these are real multiples of the corresponding brackets of the `e`'s.

Let `L` be their real span. `L` consists of `B`-skew-adjoint traceless operators, so `L <= su(V,B)`, which
has real dimension 24.

The artifact shows exactly that the 24 listed words have a `24 x 24` minor equal to
```text
P(delta) = 2^17 delta^18 (delta-1)^5 (delta+1)^5 (delta^2-2)^6 (delta^2+2) .
```
The method: the TL relations hold identically in `delta`. Rank 24 is found at `delta = 3/2`. The minor has
degree at most 82. It is interpolated exactly at 83 integer points and re-checked at 3 further points.

`P` has no root in `(sqrt 2, 2]`, and `delta = 2 cos 2x` lies there. So the complex span of the brackets is
`sl(V)`, of complex dimension 24. Hence `dim_R L >= 24`, so `L = su(V,B)` and `su(V,B) <= Lie(G)`. By (LG),
`SU(V,B)`, the connected subgroup with this Lie algebra, lies in `G^0 <= G`.

## Step 3: H = S = SU(V,B)

- *Determinant.* By (J2), `det rho(t_s) = zeta^5 w^(-4) w^4 = 1`. By (ST1) of
  `deligne-torelli-character-counts-separating-twists`, `K` is the normal closure of `t_s` in `M`, so
  `det = 1` on `rho(K)`, hence on `H`. Thus `H <= SU(V,B)`.
- *Normality.* `H` is normalized by the dense subgroup `rho(M)` of `G`, hence by `G`, hence by `SU(V,B)`.
  So `H^0` is a connected closed normal subgroup of `SU(V,B)`, and its Lie algebra is an ideal of the simple
  `su(5)`.
- *If `H^0 = 1`:* then `H` is finite and normal in the connected group `SU(V,B)`. Each conjugation orbit is
  then connected and finite, hence a point, so `H` is central, `H <= mu_5 I`.
- *But `rho(t_s) in H` is not scalar.* Its eigenvalues `zeta w^(-4)` and `zeta w` differ, since
  `w^5 = exp(-24 i x) != 1` for `x/pi` irrational.
- *Conclusion.* So `H^0 = SU(V,B) = H`. `SU(5)` is perfect, so `S = cl[H, H] = SU(V,B)`.
- *Niven.* If `delta in (sqrt 2, 2)` is rational and `x/pi` were rational, then `cos 2x = delta/2` would
  be rational with `2x/pi` rational. By (N), `delta in {0, +-1, +-2}`, which is impossible.

This proves (JC1).

## Step 4: (JC2)

**`S` and `D_zeta`.** Since `zeta^5 = 1`, `zeta I in SU(V,B) = S`, and `H/S = 1`. A primitive
`zeta' in mu_5` has `zeta' I in S` acting on `V_ab` by `zeta'^(a-b)`. So `V_ab^S != 0` forces
`5 | a - b`, and `D_zeta = infinity`.

**Distance.** The eigenvalues of `zeta-bar rho(t_s)` are `exp(96 i x/5)` and `exp(-24 i x/5)`. Since
`|e^(i theta) - 1| = 2|sin(theta/2)|`, this gives the formula for `eps_zeta`. All five `zeta` occur, by (J2).

**The twist `tau`.** All `s_i` are conjugate in `M` and `H_1(M) = Z/10`. So `chi(s_i) = eta` for
`eta in mu_10` defines the characters of `M`, and `chi(t_s) = eta^12 = eta^2`. Take `eta = zeta^3`; then
`chi_zeta(t_s) = zeta`.

`tau = chi_zeta-bar (x) rho` is honest with `tau(t_s) = zeta-bar rho(t_s)`. Scalars cancel in commutators,
so the commutators of `tau(K)` are those of `rho(K)`. Hence
`cl[H_tau, H_tau] = cl <[rho(k), rho(k')]> = S = SU(V,B)`.

**Generation.** The closed group generated by the `zeta-bar rho(t_y)`, `t_y` separating, is `H_tau`. These
are one `M`-conjugacy class by (ST1), each within `eps_zeta` of `I`.

## Step 5: (JC3)

Fix `pi` as in the definition of `Lambda*`. `pi(H)` is a compact abelian group of unitaries. So `pi|_H` is
an orthogonal sum of characters `chi` of `H`, each trivial on `[H, H]` and, by continuity, on `S`. For
`g in G`, `pi(g)` carries the `chi`-isotypic part to the `(g . chi)`-isotypic part, where
`(g . chi)(h) = chi(g^-1 h g)`. So the set `X_pi` of characters that occur is `G`-stable.

`pi(rho(t_s))` is normal with spectrum `{chi(rho(t_s)) : chi in X_pi}`. For any `chi_0 in X_pi` this gives
```text
||pi(rho(t_s)) - lambda|| = max_(chi in X_pi) |chi(rho(t_s)) - lambda| >= sup_g |chi_0(g^-1 rho(t_s) g) - lambda| .
```
This is the lower bound in (ii), and it gives (i). The listed constructions (tensor words, their subspaces
and quotients, conjugates and sums) are all continuous representations of `G`, because `rho` extends
continuously to `G` by inclusion.

**Upper bound in (ii).** Given a character `chi` of `H/S`, the induced representation `Ind_H^G chi` is
nonzero. By (PW) and Frobenius reciprocity it has an irreducible summand `pi` with `chi` in `pi|_H`.
Clifford theory for the normal subgroup `H` shows that `X_pi` is the `G`-orbit of `chi`. The isotypic parts
are permuted by `G`, and the span of one orbit's parts is `G`-invariant. Every member of the orbit kills
the normal subgroup `S`. So `pi(H)` is diagonal in an adapted basis, hence abelian, and
`||pi(rho(t_s)) - lambda|| = max over the orbit`. Taking the infimum over `chi` gives (ii).

**(iii).** The `sigma` of (CD3), or its conjugate, is `rho_ab` restricted to the `G`-invariant space
`V_ab^S`. That is a continuous representation of `G` with abelian image of `H`. And `c_ab` is an infimum
over a larger class.

**(iv).** `H/S = 1` by Step 3, so every admissible `pi` has `pi(H) = 1` and `pi(rho(t_s)) = I`.

**(v).** Apply (iv) along `x_j -> 0` with `x_j/pi` irrational at a fixed primitive `zeta`. The rescalings
realizing `zeta` exist for each `x_j` by (J2), and `zeta` lies in `mu_5 <= mu_15`. Then
`Lambda* = |1 - zeta|` while `eps_zeta -> 0`, which contradicts any such `f`.

The last sentence of (JC3 v) is Step 4's character `chi_zeta`, together with (iv).

## Step 6: (JC4)

**(i).** For `k, k' in K`, the commutator
`[sigma(k) (x) tau(k), sigma(k') (x) tau(k')] = I (x) [tau(k), tau(k')]`, since `sigma(K)` is abelian. So
the closed derived subgroup of the Torelli image of `sigma (x) tau` is `I (x) cl[H_tau, H_tau]`, which
contains `I (x) mu I = mu I`. For the norm, split
`sigma(t) (x) tau(t) - lambda = (sigma(t) - lambda) (x) tau(t) + lambda (I (x) (tau(t) - I))`.
The consequence follows by applying this to `sigma_j` witnessing `1/3 in Z_ab` and to absorbers `tau_j`;
its contrapositive is the (TAP) statement.

**(ii).** Let `pi` be a continuous representation of `G` and suppose `pi(g) = mu I` with `g in SU(V,B)`.
`ker pi cap SU(V,B)` is closed and normal in `SU(V,B)`, so it is `SU(V,B)` or finite central (as in Step 3).
- In the first case `mu = 1`.
- In the second case, `h -> h g h^-1 g^-1` maps the connected group `SU(V,B)` continuously into the finite
  set `ker pi cap mu_5 I`, and sends `1` to `1`. So it is identically `1`, `g` is central, and
  `mu^5 = 1`.

Also `cl[pi(H), pi(H)] = pi(S) = pi(SU(V,B))` by compactness. Twisting `pi o rho` by a character of `M` does
not change commutators. So no representation of the form `chi (x) (pi o rho)` has `omega I` in its closed
derived Torelli subgroup. QED.
