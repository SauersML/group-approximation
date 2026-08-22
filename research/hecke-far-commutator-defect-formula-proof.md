---
rg: 2
id: hecke-far-commutator-defect-formula-proof
kind: route
title: Gram positivity, Schlichting extension, Howe-Moore mixing, mean ergodic identification
target: hecke-far-commutator-defect-formula
requires: []
---

Write `xi_g = pi(g) k pi(g)*`, a unit vector of `L^2(M,tau)`.

**Positivity and bi-invariance.**  A direct trace computation gives
`psi_k(h^(-1) g) = <xi_g, xi_h>`, so `(psi_k(h^(-1)g))_(g,h)` is a Gram
matrix and `psi_k` is positive definite.  Since `k` commutes with
`pi(Lambda)`, `xi_(lambda) = k` for `lambda in Lambda`, whence
`psi_k|_Lambda = 1`; and `psi_k(lambda g mu) = psi_k(g)` for
`lambda, mu in Lambda` by the same commutation plus trace invariance
under `Ad pi(lambda)`.  Expanding
`||k pi(g) - pi(g) k||_2^2 = 2 - 2 Re tau(pi(g)* k* pi(g) k)` and
cycling the trace gives `(HFD2)`.

**Schlichting extension.**  `psi_k` is constant on `Lambda`-double
cosets, hence continuous for the Hecke topology on `Gamma` whose basic
identity neighbourhoods are the finite intersections
`cap_(gamma in F) gamma Lambda gamma^(-1)`.  The completion map
`Gamma -> G` has dense image with finite central kernel contained in
`Lambda`, so `psi_k` descends and extends by density to a `K`-bi-
invariant positive definite function on `G`, locally constant since `K`
is open.  For `(Gamma,Lambda) = (SL_n(Z[1/p]), SL_n(Z))` the completion
is `G = PSL_n(Q_p)` with `K` the image of `SL_n(Z_p)`
(Shalom--Willis, Tzanev); `Gamma` is dense by strong approximation.

**Howe--Moore splitting.**  Let `(H, rho, xi)` be the GNS triple of the
extended function on `G` and split `H = H^G + (H^G)^perp` into
`G`-invariant vectors and their complement.  `G` is, modulo finite
kernel, simple over a local field, so by Howe--Moore every matrix
coefficient of `rho` on `(H^G)^perp` vanishes at infinity.  Writing
`xi = xi_0 + xi_1` along the splitting,

```text
psi_k(g) = ||xi_0||^2 + <rho(g) xi_1, xi_1> -> ||xi_0||^2
```

along the cofinite double-coset filter, because a compact subset of `G`
meets only finitely many `K`-double cosets.

**Mean ergodic identification of the constant.**  The GNS space embeds
in `L^2(M)` as the closed `Ad pi(Gamma)`-cyclic subspace of `k`, and
`G`-invariance of a vector there is `Gamma`-invariance by density.  The
`Ad pi(Gamma)`-invariant vectors of `L^2(M)` are exactly
`L^2(pi(Gamma)' cap M)`, and the orthogonal projection onto them is the
trace-preserving conditional expectation `E`.  By the von Neumann mean
ergodic theorem, `E(k)` lies in the closed convex hull of the orbit
`{xi_g}`, hence in the cyclic subspace, so the projection of `k` there
is `E(k)` and `||xi_0||^2 = ||E(k)||_2^2`.  This proves `(HFD3)`, and
`(HFD4)` follows from `(HFD2)`.

**Consequences.**  If `||E(k)||_2 = 1` then `E(k) = k` since `k` is a
unit vector, so `k in pi(Gamma)' cap M`.  If `E(k) = 0` the far defect
tends to `2`, i.e. `<xi_gamma, k> -> 0`.  (Corrected 2026-08-21: the
coefficient function of the `K`-fixed vector `delta_(eK)` of `L^2(G/K)`
is the indicator `1_K`, since `K` is open and `G/K` discrete -- NOT the
Harish-Chandra `Xi` profile; and the canonical enemy really has
`psi_k = 1_Lambda` exactly.  In the general case `0 < s < 1` temperedness
of the `c_0` component is not forced either: `PSL_n(Q_p)`, `n >= 3`, has
spherical complementary series, which property (T) does not exclude.)
