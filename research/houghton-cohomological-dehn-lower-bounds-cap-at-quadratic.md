---
rg: 2
id: houghton-cohomological-dehn-lower-bounds-cap-at-quadratic
kind: claim
title: "Cocycle and central-extension lower bounds for the Dehn function of H_n (n >= 3) never exceed x^2 unless the coefficient module has H^1 of the finitary kernel nonzero"
distinct_from:
  houghton-groups-have-at-least-quadratic-dehn-function: that is the lower bound x^2 itself; this says a whole class of lower-bound certificates cannot give anything beyond x^2.
  some-houghton-group-has-superquadratic-dehn-function: that is the open assertion that some H_n is not quadratic; this is an obstruction to one class of proofs of it, and says nothing about whether it is true.
---

Fix `n >= 3`, a finite presentation `<S | R>` of Houghton's group `G = H_n`
with presentation complex `X` and Cayley complex `X~`, the translation map
`π : G -> Q = Z^(n-1)` and its kernel `K = FSym(Y_n)`.

A **cocycle certificate** is a pair `(V, ω)`:

- `V` is a real Banach space on which `G` acts by linear isometries;
- `ω` assigns to each 2-cell of `X~` a vector of `V`, `G`-equivariantly;
- the value `ω(D) = Σ_cells ±ω(cell)` of a van Kampen diagram `D` depends only
  on its boundary word.

Every van Kampen diagram of a null-homotopic word `w` has at least
`||ω(D_w)|| / sup ||ω||` cells, so `(V, ω)` certifies the lower bound
`δ(x) >= L_ω(x) := max { ||ω(D_w)|| : |w| <= x } / sup ||ω||`.
Gersten-type 2-cocycle bounds (`V = R`), bounds from the distortion of a
central `Z` (see (C)), and bounds with finite-dimensional unitary or orthogonal
twisting are all of this form.

**Claim.**

- **(A)** If `H^1(K; V) = 0`, then `L_ω(x) <= C x^2` for a constant `C = C(ω)`.
  This holds in particular for every finite-dimensional `V` and for `V = R`.
- **(B)** For every real `G`-module `V`: `H^2(K; V) = 0`, and
  `H^1(K; V) = lim^1_i V^(F_i)` for any exhaustion `F_1 ⊂ F_2 ⊂ ...` of `K` by
  finite subgroups. So `H^1(K; V) = 0` whenever the fixed-point tower
  `V^(F_i)` stabilizes.
- **(C)** For every central extension `1 -> Z = <z> -> E -> G -> 1` with `E`
  finitely generated, `|z^N|_E >= c sqrt(|N|)` for some `c > 0`. So a central
  `Z` in an extension of `H_n` is at most quadratically distorted.
- **(D)** Every finitely generated abelian subgroup of `H_n` is undistorted.

**Consequence.** A proof of
`some-houghton-group-has-superquadratic-dehn-function` cannot come from:

- a 2-cocycle with trivial or finite-dimensional coefficients;
- a central extension;
- distortion of abelian subgroups.

A cocycle certificate that beats `x^2` must use an infinite-dimensional
isometric module whose fixed-point tower under the finite symmetric groups
`F_i = Sym({1..n} x {1..i})` fails the Mittag-Leffler condition badly enough
that `lim^1_i V^(F_i) != 0`. The module `ℓ^∞(G)` is the basic example.
Certificates over `ℓ^∞(G)` include every bounded non-equivariant real
2-cochain whose diagram values depend only on the boundary. Those cochains are
the feasible points of the LP dual of the real homological filling problem.

Where every member of the killed class dies: at the inflation step, where
`ω(D)` becomes an area pairing in `Z^(n-1)` plus a boundary term.

Proof: `houghton-cohomological-dehn-lower-bounds-cap-proof`.
