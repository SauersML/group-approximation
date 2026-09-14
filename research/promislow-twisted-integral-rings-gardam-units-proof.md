---
rg: 2
id: promislow-twisted-integral-rings-gardam-units-proof
kind: route
title: Grade R[P] by a homomorphism to (Z/4)^2 and read the degree-zero subring as a twisted integral group ring
target: promislow-twisted-integral-rings-carry-gardam-units
requires:
  - unit-conjecture-fails-over-complex-numbers
---

Notation is as in `promislow-twisted-integral-rings-carry-gardam-units`, with
`x = a^2`, `y = b^2`, `R = Z[s,t]/(s^4+1, t^4+1)`.

**Step 1 (abelianization).** Abelianizing `b^-1 a^2 b = a^-2` gives `4a = 0`,
and abelianizing `a^-1 b^2 a = b^-2` gives `4b = 0`. So `P^ab = Z/4 + Z/4`, and
`rho(a) = (1,0)`, `rho(b) = (0,1)` defines a homomorphism `rho: P -> (Z/4)^2`.

**Step 2 (the cocycle).** Put `f(g) = s^it(g) t^jt(g)`, a unit of `R`. Since
`it(gh) = it(g) + it(h) mod 4` and `s^4 = -1`, we get
`f(g) f(h) = c(g,h) f(gh)` with `c` as in item 3 of the claim. So `c` is a
normalized 2-cocycle with values in `{+-1}`: it is a coboundary in `R^x` whose
values happen to be signs. Let `ft: P -> Z/8` take the values `it(g)`. Then
`ft(g) + ft(h) - ft(gh)` is `4` exactly when `it(g) + it(h) >= 4`, and `0`
otherwise. This is the standard cocycle representing `beta(rho_1)`. The same
holds for `jt` and `rho_2`. Since `beta` is additive,
`[c] = beta(rho_1) + beta(rho_2) = beta(rho_1 + rho_2)`.

**Step 3 (grading).** `R` is free over `Z` with basis `s^i t^j`,
`0 <= i, j < 4`. Setting `R_(i,j) = Z s^i t^j` makes `R` a `(Z/4)^2`-graded
ring, because `s^i t^j s^k t^l = +- s^((i+k) mod 4) t^((j+l) mod 4)`. Grade
`R[P]` by `deg(r g) = deg(r) - rho(g)` for homogeneous `r`. Coefficients are
central and `rho` is a homomorphism, so this is a ring grading. Its
degree-zero part is the direct sum over `g` of `Z f(g) g`.

**Step 4 (the twisted ring).** The map `phi: Z^c[P] -> R[P]`,
`gbar -> f(g) g`, is additive and injective: `f(g)` is a signed basis
element of `R`. It is multiplicative, since
`phi(gbar) phi(hbar) = f(g) f(h) gh = c(g,h) f(gh) gh = phi(gbar hbar)`. By
Step 3 its image is exactly the degree-zero subring `R[P]_0`.

**Step 5 (homogeneous units).** Let `alpha in R[P]_0` be a unit of `R[P]` with
inverse `beta = sum_d beta_d` split into homogeneous components. The degree-zero
component of `alpha beta = 1` is `alpha beta_0 = 1`, and that of
`beta alpha = 1` is `beta_0 alpha = 1`. So `beta_0` is a two-sided inverse and
`beta = beta_0 in R[P]_0`. Hence `phi` identifies the units of `Z^c[P]` with
the units of `R[P]` lying in `R[P]_0`.

**Step 6 (Gardam's unit).** Gardam's `alpha, beta in R[P]` satisfy
`alpha beta = beta alpha = 1`, and every coefficient is a signed monomial
(`unit-conjecture-fails-over-complex-numbers`, rechecked exactly in
`research/artifacts/gardam-support-pair-gsp.py`). The script
`research/artifacts/ideas-kaplansky-atiyah-2-2026-09-14/twisted_integral_unit_check.py`
checks exactly that the class `(i mod 4, j mod 4)` of the coefficient at `g`
equals `rho(g)`, for all 21 support elements of `alpha` and of `beta` (log
line `(1)`). So `alpha, beta in R[P]_0`, and `abar = phi^-1(alpha)` is a unit
of `Z^c[P]` with coefficients `+-1` and support of size 21. A unit `n gbar`
needs `n = +-1`, so trivial units have support 1 and `abar` is nontrivial. The
script also multiplies directly in `Z^c[P]`:
`abar bbar = bbar abar = 1` (log line `(2)`).

**Step 7 (the class is nonzero).** Put `psi = rho_1 + rho_2`, so `psi(a) = 1`
and `psi` is onto `Z/4`. By exactness of
`H^1(P; Z/8) -> H^1(P; Z/4) -> H^2(P; Z/2)`, `beta(psi) = 0` exactly when
`psi` lifts to a homomorphism `P -> Z/8`. `P^ab` has exponent 4, so every
homomorphism `P -> Z/8` lands in `2Z/8`, whose reduction mod 4 is `2Z/4`. An
onto `psi` does not lift, so `[c] != 0`.

**Step 8 (the four classes).**
- The kernel of `beta` is the image of `H^1(P; Z/8)`. As in Step 7, that image
  lies in `2 H^1(P; Z/4)`. Conversely `2 chi` lifts as `chi` composed with
  `Z/4 = 2Z/8 <= Z/8`. So `ker beta = 2 H^1(P; Z/4)`, and `beta` induces an
  injection `H^1(P; Z/2) = H^1(P; Z/4)/2 -> H^2(P; Z/2)`.
- `P` is torsion-free and acts freely and cocompactly on `R^3` by the affine
  isometries of the script, so `M = R^3/P` is a closed aspherical 3-manifold.
- Poincare duality mod 2 gives
  `|H^2(P; Z/2)| = |H_1(M; Z/2)| = |P^ab / 2| = 4`. So the injection is an
  isomorphism.

This is item 1. Cohomologous cocycles `c' = c dh` with `h: P -> {+-1}` give the
isomorphism `gbar -> h(g) gbar`. It preserves supports and trivial units. With
`c = 0` this is item 2.

**Step 9 (transitivity).**
- **θ is an automorphism.** Let `theta(a) = b` and `theta(b) = ab`. The
  relations are respected:
  - `(ab)^-1 b^2 (ab) = b^-1 (a^-1 b^2 a) b = b^-2 = theta(a^-2)`;
  - `b^-1 (ab)^2 b = (ab)^-2`, because conjugation by `b` inverts `z = (ab)^2`.

  `theta` is onto because `a = (ab) b^-1`. `P` is finitely generated and
  residually finite (virtually `Z^3`), hence Hopfian, so `theta` is an
  automorphism.
- **Action on classes.** On `H^1(P; Z/2)`, `chi -> chi o theta` sends
  `(chi(a), chi(b))` to `(chi(b), chi(a) + chi(b))`. This cycles
  `(1,1) -> (1,0) -> (0,1) -> (1,1)`. The Gardam class is `psi mod 2 = (1,1)`.
- **Transfer of units.** `theta` induces
  `Z^(theta* c)[P] = Z^c[P]` by `gbar -> theta(g)bar`, and `beta` is natural.
  So each nonzero class carries the image of `abar`, with coefficients `+-1`
  and support of size 21. This is item 4.

**Step 10 (item 5).** The ring map `R -> Z[zeta_8]`, `s, t -> zeta_8`, is well
defined because `zeta_8^4 = -1`. Composing with `phi` gives a ring map
`Z^c[P] -> Z[zeta_8][P]` that keeps the support of every element. So it sends
nontrivial units to units with support of size at least 2, which are
nontrivial. QED
