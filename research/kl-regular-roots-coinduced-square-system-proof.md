---
rg: 2
id: kl-regular-roots-coinduced-square-system-proof
kind: route
title: Embed the extension in a coinduced wreath product over the root group, read the equation as a square system over the kernel, and solve finite subsystems with Howie or Krstic
target: kl-regular-roots-lift-through-locally-indicable-kernels
requires: []
artifacts:
  - research/artifacts/hl-howie-systems-2026-09-13.md
---

Notation of the target. Imports:
- [How81] a finite non-singular system of equations over a locally indicable
  group is solvable;
- [Kr85] a finite `p`-nonsingular system over a locally `p`-indicable group is
  solvable.

Both are pinned in the artifact, l.264--274. A system of `n` equations in `n`
unknowns is non-singular (resp. `p`-nonsingular) when the determinant of its
exponent-sum matrix is non-zero (resp. not divisible by `p`). "Solvable" means
that some overgroup contains a solution. For a system `{r_i}` over `H` with
unknowns `Y`, that is the same as injectivity of
`H -> (H * F(Y))/<<r_i>>`.

## 1. Item 1

**1a. Coinduced embedding.** By Kaloujnine--Krasner there is an injective
homomorphism `G -> Map(F, H) ⋊ F`, unrestricted wreath product, with `F`
acting by `(f·q)(x) = q(f^(-1) x)` and `g -> (phi_g, gH)`.

Let `Gamma >= F` and choose a right transversal `R` of `F` in `Gamma`. Every
`x in Gamma` is uniquely `x = f r` with `f in F`, `r in R`. Define
`iota : Map(F,H) -> Map(Gamma,H)` by `iota(q)(f r) = q(f)`. It is an injective
homomorphism, and it is `F`-equivariant:
`(f'·iota(q))(f r) = iota(q)(f'^(-1) f r) = q(f'^(-1) f) = iota(f'·q)(f r)`.
So `(q, f) -> (iota(q), f)` embeds `Map(F,H) ⋊ F` in
`W_H = Map(Gamma, H) ⋊ Gamma`. For any group `L >= H` we have
`W_H <= W_L = Map(Gamma, L) ⋊ Gamma`. Composing gives an embedding
`G -> W_H`, `g -> (psi_g, gH)`, with `psi_g in Map(Gamma, H)`.

**1b. The square system.** The multiplication in `W_L` is
`(p_1, x_1)(p_2, x_2) = (p_1 · (x_1·p_2), x_1 x_2)`. Take unknowns
`p_y`, `y in Gamma`, and put `t = (p, tau)`. Then
`t^(-1) = (tau^(-1)·p^(-1), tau^(-1))`. Multiplying the letters of `w` gives
`w(t) = (Phi, w-(tau)) = (Phi, 1)`, with

    Phi = prod_j ( pi_(j-1) · u_j ),

where `u_j = psi_g` for a coefficient letter `g`, `u_j = p` for `t`, and
`pi_(j-1)·u_j = s'_j · p^(-1)` with `s'_j = pi_(j-1) tau^(-1)` for `t^(-1)`.
Write `s'_j = pi_(j-1)` for a `t` letter. Since `(x·q)(z) = q(x^(-1) z)`, the
coordinate `Phi(z)` is a word `r_z` in constants `psi_g(x^(-1) z) in H` and in
unknowns `p_(s'_j^(-1) z)^(eps_j)`, where `eps_j = ±1` is the exponent of the
`j`-th `t`-letter. Its exponent-sum row is

    E(z, y) = sum over t-letters j with s'_j^(-1) z = y of eps_j.

Each row has finite support `{s'_j^(-1) z}`.

**1c. Rows are independent.** Let `lambda : Gamma -> Q` be finitely
supported with `sum_z lambda(z) E(z, y) = 0` for all `y`. The left side equals
`sum_j eps_j lambda(s'_j y)`. Put `mu = sum_z lambda(z) z^(-1) in Q[Gamma]`.
Since `D = sum_j eps_j s'_j`, the coefficient of `y^(-1)` in `mu D` is
`sum_z sum_(j : z^(-1) s'_j = y^(-1)) lambda(z) eps_j = sum_j eps_j lambda(s'_j y)`.
So `mu D = 0`. Clearing denominators gives an integral `mu` with `mu D = 0`,
so `mu = 0` by regularity, and hence `lambda = 0`. The same computation over
`F_p` gives independence mod `p` from regularity over `F_p`.

**1d. Finite subsystems.** Let `S ⊂ Gamma` be finite and `T` the finite set of
unknowns occurring in `{r_z : z in S}`. The `S × T` exponent matrix contains
the full rows, so it has rank `|S|` (over `Q`, resp. `F_p`). Choose
`T' ⊆ T` with `|T'| = |S|` and non-zero minor on `S × T'` (resp. a minor that
is non-zero mod `p`, hence an integer not divisible by `p`). Substituting
`p_y = 1` for `y in T \ T'` gives a square system over `H` in the unknowns
`T'` with the same exponent matrix on `T'`. It is non-singular (resp.
`p`-nonsingular), so [How81] (resp. [Kr85]) gives
`H -> (H * F(T'))/<<r_z|_(p_y=1, y notin T'), z in S>>` injective. That group is
a quotient of `(H * F(T))/<<r_z : z in S>>` by the relations `p_y = 1`, so `H`
injects into the latter as well.

**1e. The whole system.** Let `L = (H * F(p_y : y in Gamma))/<<r_z : z in Gamma>>`.
If `h in H` dies in `L`, it is a product of finitely many conjugates of
relators `r_z^(±1)` in `H * F(Y)`. So `h` dies in the finite subsystem, and
`h = 1` by 1d. So `H <= L`. In `W_L`, `t = (p, tau)` with `p(y) = [p_y]` gives
`w(t) = (Phi(p), 1) = (1, 1)`.

**1f. Conclusion.** The homomorphism `G * <t> -> W_L`, given by the embedding
of 1a on `G` and `t -> (p, tau)`, kills `w`. So it factors through
`(G * <t>)/<<w>>`, and its restriction to `G` is injective. Hence
`G -> (G * <t>)/<<w>>` is injective.

## 2. Item 2

By the localization argument (for `G >= P`, `G_w = G *_P P_w`, normal form in
amalgams) it suffices to treat `P = H<g>`: all coefficients of `w` lie in `P`,
and `H <| P` with `P/H = <c>`, `c = gH` of order `d`. Take `Gamma = P/H`. Since
`gcd(m, d) = 1`, choose `k` with `m k ≡ -1 (mod d)` and put `tau = c^k`.

Every coefficient of `V` maps to `1`, so `w- = t^(eps_1) ... t^(eps_L) c`, and
`w-(tau) = tau^m c = c^(mk + 1) = 1`. All letters of `V` precede `g`, so the
prefix of a `t`-letter reaching height `e+1` from `e` is `tau^e`. The shifted
prefix of a `t^(-1)`-letter going from `e+1` to `e` is `tau^(e+1) tau^(-1) = tau^e`.
So `D = sum_e n_e tau^e`, where `n_e` is the net number of crossings of
`[e, e+1]` by the height walk from `0` to `m`. That is `n_e = 1` for
`0 <= e < m` and `n_e = 0` otherwise (for `m > 0`; for `m < 0` it is
`D = -(tau^(-1) + ... + tau^m)`, handled identically). So
`D = 1 + tau + ... + tau^(m-1)`.

Here `gcd(k, d) = 1`, so `tau` generates `Gamma = C_d`. For a character
`chi(tau) = omega`, `omega^d = 1`:
- if `omega = 1`, then `chi(D) = m != 0`;
- otherwise `omega^m != 1` because `gcd(m, d) = 1`, so
  `chi(D) = (1 - omega^m)/(1 - omega) != 0`.

So `D` is a unit in `C[C_d]`, hence in `Q[C_d]`, and no non-zero `mu` has
`mu D = 0`. Item 1 applies.

## 3. Item 3

Build `X` from a one-vertex CW model of `K(F,1)`. Coefficient letters are
loops in it, the 1-cell `e^1` is the letter `t`, and `e^2` is attached along
`w-`. Then `pi_1(X) = Gamma_F`. Let `p : X~ -> X` be the universal cover and
`Y = p^(-1)(K(F,1))`.
- Since `F -> Gamma_F` is injective, each component of `Y` is the universal
  cover of `K(F,1)`, which is contractible.
- The relative cellular chain complex `C_*(X~, Y)` is `Z[Gamma_F]` in degrees 1
  and 2 (lifts of `e^1`, `e^2`) and `0` elsewhere.
- Label lifts by `Gamma_F` using a base vertex `v`, with `gamma e~^1` running
  from `gamma v` to `gamma tau v`.
- Along the lifted boundary of `e~^2` from `v`, coefficient letters stay in `Y`
  and contribute nothing to relative chains. A `t`-letter at vertex `pi_(j-1) v`
  traverses `pi_(j-1) e~^1` positively, and a `t^(-1)`-letter traverses
  `pi_(j-1) tau^(-1) e~^1` negatively.
- So `d_2(gamma e~^2) = gamma D e~^1`, and `ker d_2 = {mu : mu D = 0}`.

With no relative 3-cells, `H_2(X~, Y) = ker d_2`. The exact sequence
`H_2(Y) = 0 -> H_2(X~) -> H_2(X~, Y) -> H_1(Y) = 0` and Hurewicz give
`ker d_2 ≅ H_2(X~) ≅ pi_2(X)`.

Suppose `pi_2(X) = 0`. Then `H_n(X~) = H_n(X~, Y) = 0` for `n >= 2` (for
`n >= 3` there are no relative cells), and `X~` is simply connected, so it is
contractible. With `F_p` coefficients the same sequence gives
`ker(d_2 ⊗ F_p) = H_2(X~, Y; F_p) ≅ H_2(X~; F_p) = 0`, so the universal root is
regular over every `F_p`. Item 1 gives the stated injectivity. Finite `F`
injects into `Gamma_F` by Gerstenhaber--Rothaus.

## 4. Item 4

Every root `tau` of `w-` in a group `Gamma` is, after conjugating by the
conjugator in `F * <t>`, a root of `t^m c`, and conjugation multiplies `D` on
the left by a unit `gamma` of `Z[Gamma]` without changing the left annihilator.
If `u` is conjugate to `t^m c` by `x`, then `d(x u x^(-1)) = dx + x·du - x u x^(-1)·dx`,
and at a root `x u x^(-1) = 1` this is `x · du`. So assume `w- = t^m c`.

Then `tau^m = c^(-1)` has order `d`, so `tau` has finite order `n` with
`n / gcd(n, m) = d`. If `gcd(n, m) = 1`, then `n = d` and `gcd(m, d) = 1`, a
contradiction. So some `omega != 1` with `omega^n = 1` has `omega^m = 1`.

`D = 1 + tau + ... + tau^(m-1)` lies in `Z[<tau>] = Z[C_n]`, and its character
at `omega` is `0`, so `D` is a zero divisor in the commutative ring `Z[C_n]`:
there is `mu != 0` in `Z[C_n] ⊆ Z[Gamma]` with `mu D = 0`. For `m < 0` use
`D = -tau^m (1 + ... + tau^(|m|-1))`. So the root is not regular.

The word `t^m c` is injective for every group containing `c`: its adjunction
is the amalgam `G *_(c = t^(-m)) <t>`, over `<c> ≅ <t^m>` in `<t | t^(md)>`.
