---
rg: 2
id: lifted-thompson-t-is-a-torus-knot-group-quotient-proof
kind: route
title: Lift the order-4 and order-3 generators of T with translation numbers 1/4 and 1/3; the relation a^4 = b^3 = z is forced, and generation passes to commutants
target: lifted-thompson-t-is-a-torus-knot-group-quotient
requires:
  - funar-sergiescu-lifted-thompson-t-is-t311
---

Notation as in the target.  `tau` is the translation number on
homeomorphisms of `R` that commute with `z`.  It satisfies:
- `tau(g^m) = m tau(g)`;
- `tau` is conjugation-invariant;
- `tau(g z^j) = tau(g) + j`.

A lift of the identity of `S^1` is `z^m`, and `tau(z^m) = m`.

## Item 1

By item 1 of `funar-sergiescu-lifted-thompson-t-is-t311`, `T = <alpha, beta>`
with `alpha^4 = beta^3 = 1`.

**Step 1 (the roots are forced up to sign).**  Let `a0` be a lift of `alpha`.
Then `a0^4` lifts the identity, so `a0^4 = z^m`.  If `gcd(m, 4) = d > 1`,
put `w = a0^(4/d) z^(-m/d)`.  Since `z` is central, `w^d = a0^4 z^(-m) = 1`.
An orientation-preserving homeomorphism of `R` of finite order is the
identity: if `w(t) > t` then `w^d(t) > t`, and similarly for `<`.  So
`w = 1`, and `a0^(4/d) = z^(m/d)` lifts the identity.  Therefore
`alpha^(4/d)` has a lift equal to a translation, that is,
`alpha^(4/d) = 1` on the circle.  This contradicts the order of `alpha`
being 4.  So `m` is odd.  Put `a = a0 z^j` with `j` chosen so that
`m + 4j = ±1`.  Then `a^4 = z^(ε_1)` with `ε_1 in {1, -1}`.  In the same way
there is a lift `b` of `beta` with `b^3 = z^(ε_2)`.

The exact computation in `experiments/torus-knot-cover-2026-09-17/output.txt`,
recorded in `funar-sergiescu-lifted-thompson-t-is-t311`, gives
`ε_1 = ε_2 = 1`.  The argument does not need this.
- If `ε_1 = -ε_2`, replace `b` by `b^(-1)`.
- If both are `-1`, replace `z` by `z^(-1)`, which generates the same
  centre.  Eigencorners of `rho(z)` and of `rho(z)^(-1)` are the same
  projections, with the eigenvalue inverted.

**Step 2 (generation).**  `<a, b>` contains `a^4 = z` and maps onto
`<alpha, beta> = T`.  Every `g in T̄` is `g = w(a, b) z^j` for a word `w`
mapping to the image of `g`.  So `<a, b> = T̄`.

**Step 3 (the surjection).**  `x -> a`, `y -> b` respects the single relator
`x^4 y^(-3)`, since `a^4 = z = b^3`.  So it defines `phi : K -> T̄`, which is
onto by Step 2, and `phi(c) = z`.

**Step 4 (the kernel).**  By item 2 of the imported claim, `T̄` is presented
on `a, b, z` by the relators listed there together with `[a, z] = [b, z] = 1`.
Eliminate `z = a^4` by a Tietze move.
- `b^3 = z` becomes `x^4 = y^3`.
- `[a, z] = 1` becomes `[x, x^4] = 1`, which is trivial.
- `[b, z] = 1` becomes `[y, x^4] = 1`, which follows from `x^4 = y^3`.

So
`ker(phi) = <<(yx)^5 c^(-3), [yxy, x^2 yxy x^2], [yxy, x^2 y^2 x^2 yxy x^2 y x^2]>>`.

## Item 2

`sigma = rho o phi` is a homomorphism `K -> U(Q)`.  Its image is
`rho(phi(K)) = rho(T̄)`, because `phi` is onto.  So the commutants agree.
Directly, a `P in Q` commutes with `rho(T̄)` if and only if it commutes with
`rho(a) = sigma(x)` and `rho(b) = sigma(y)`, which generate the image.
Also `sigma(c) = rho(phi(c)) = rho(z)`.

The statement `lifted-thompson-t-centre-has-commutant-eigencorners` asks,
for every `rho` with `rho(z) != 1`, for a nonzero projection `P` in
`rho(T̄)' ∩ Q` and some `lambda != 1` with `rho(z) P = lambda P`.  This is the
statement of `torus-knot-group-k34-has-central-eigencorners` for `sigma`.
Conversely, a `sigma` that kills `ker(phi)` factors as `rho o phi`.

## Item 3

`K` is presented on the two generators by the single relator.  So a
homomorphism `K -> U(Q)` is exactly a pair of unitaries `X, Y` in `Q` with
`X^4 = Y^3`.  By (L1) of
`central-eigencorners-die-over-full-radical-quotients-proof`, `X` and `Y`
lift to unitary sequences `X_n, Y_n`.  Then `X^4 = Y^3` in `Q` means
`||X_n^4 - Y_n^3|| -> 0`.  Conversely, such sequences define a pair in `Q`.
The relators of Step 4 go to `1` in `Q` if and only if their values on
`(X_n, Y_n)` tend to `1` in norm.
