---
rg: 2
id: bounded-degree-two-primitives-for-higher-rank-lattices
kind: claim
title: Operator-bounded degree-two primitives for Ad-modules of SL_N(Z), N at least 4
distinct_from:
  sln-z-flexibly-hs-stable: that is the stability conclusion; this is the single cohomological input from which the normalized-HS Newton iteration of `hs-stability-from-bounded-degree-two-primitives` derives it -- a statement about 2-cocycles, not about almost-representations.
  sl3z-regular-microstates-are-congruence-correctable: that is the rank-3 correctability hole attacked through extreme points; this is a rank-at-least-4 input living in degree-2 cohomology, where Bader--Sauer vanishing exists and SL_3 has none.
---

Claim.  Let `N >= 4`, `Gamma = SL_N(Z)`, and let `M` be a tracial
matrix ultraproduct with a unitary representation `pi` of `Gamma`
acting on `L^2(M)` by `Ad pi`.  There is a constant `C_N` such that
every 2-cocycle `c` of `Gamma` (on the cells of a fixed finite
presentation complex) with values in `M` which is a coboundary in
`L^2(M)` admits a primitive `y` (a 1-cochain with `delta y = c`)
satisfying BOTH

```text
|| y ||_2   <= C_N || c ||_2          (the usual modulus), and
|| y ||_op  <= C_N || c ||_op         (operator-norm control).
```

The first inequality is a quantitative form of Bader--Sauer's
property `(T_(N-2))` for the Ad-module (degree-2 gap); the second is
new and is the whole point.

## Attempts

- **Why degree one is free and degree two is not (the precise
  obstruction).**  In degree one, Kazhdan's argument produces the
  primitive of a 1-cocycle `b` as the fixed point of the affine
  isometric action, a 2-norm limit of Cesaro averages of the orbit
  points `b(g)`; since `|| b(g) ||_op <= 2` for cocycles coming from
  unitaries and the operator norm is lower semicontinuous on
  2-norm-bounded sets, the primitive is operator-bounded for free.
  In degree two the Hodge primitive `y = delta^* Delta_2^(-1) c` has
  no averaging structure: a Neumann-series inverse
  `Delta_2^(-1) = (1/mu) sum_n (1 - Delta_2/mu)^n` contracts in
  2-norm by `theta = 1 - lambda/mu` per term while its
  `l^1`-coefficient norm grows by `C = 1 + ||Delta_2||_(l^1)/mu`;
  truncating at `n ~ log(1/eps)` costs an operator-norm factor
  `eps^(-kappa)` with `kappa = log C / log(1/theta) ->
  ||Delta_2||_(l^1) / lambda >= 1`, independent of `mu`.  So the
  naive primitive is NOT operator-controlled, and this is exactly
  why no normalized-HS version of the De Chiffre--Glebsky--Lubotzky--
  Thom criterion is in the literature.  What would suffice: a
  positive-coefficient (averaging, `l^1`-norm one) expansion of the
  harmonic projection in degree two -- a Garland-type local-averaging
  formula -- or any SOS certificate for the degree-2 gap whose
  Neumann expansion has `kappa < 1`.
- **What is known on the gap side (source-verified 2026-08-21).**
  Bader--Sauer [arXiv:2308.06517, Theorem A]: `SL_n(R)` and all its
  lattices have property `(T_(n-2))` in the UNREDUCED sense --
  `H^j(Gamma, V) = 0` for `1 <= j <= n-2` and every unitary `V`
  without invariant vectors (an earlier note in this lane said
  "reduced"; that was too weak).  So for `N >= 4` the degree-2
  vanishing holds for the single ultraproduct Ad-module
  `L^2(M) minus invariants`, and the open mapping theorem gives a
  2-norm modulus for THAT module with no uniformity issue; the
  invariant-vector part is harmless since `H^2(SL_N(Z); C) = 0` for
  `N >= 3` (Borel stable range, Soule at `N = 3`).  Consequently
  Bader--Lubotzky--Sauer--Weinberger [BLSW23, cited in
  arXiv:2512.09180] obtain FROBENIUS (unnormalized) stability for
  higher-rank lattices of rank at least three, i.e. `SL_N(Z)` for
  `N >= 4`; `SL_3(Z)` is open even for Frobenius stability
  (arXiv:2512.09180 also shows `(T_2)` is not necessary for Frobenius
  stability).  The norm gap is therefore the ENTIRE distance between
  the literature and the correctability input at rank >= 4: a
  normalized defect `delta` is a Frobenius defect `sqrt(d) delta`,
  far outside any Newton basin, so Frobenius stability cannot be
  scaled down; the normalized iteration must run natively, and its
  only new need is the operator bound of this claim.  The
  Kaluba--Mizerka--Nowak certified-SOS program (explicit degree-1
  gaps at `SL_3`, degree-2 inducing results) is the natural source of
  an explicit positive-coefficient or low-`kappa` certificate.
- **Why the naive Garland route does not supply the positive-coefficient
  formula (2026-08-21).**  Garland's method DOES give a positive,
  `l^1`-norm-one, local-averaging expression for the harmonic projection
  --- the missing ingredient named above --- because it writes the global
  Laplacian gap as an average of LINK Laplacian gaps, and the links of the
  `SL_N(Q_p)` Bruhat--Tits building are the spherical buildings of
  `SL_N(F_p)`, whose degree-2 gaps are uniform and independent of the
  coefficient module.  But it needs the group to act on the building with
  a FINITE (cocompact) quotient, and `SL_N(Z)` does not act on the
  `SL_N(Q_p)` building at all discretely (it is dense in the vertex
  stabiliser `SL_N(Z_p)`).  The group that does act is `SL_N(Z[1/p])`, an
  IRREDUCIBLE NON-UNIFORM lattice in `SL_N(R) x SL_N(Q_p)`; its action on
  the building alone has non-compact quotient (the `R`-factor cusps), so
  the local-to-global averaging degenerates exactly at the cusps.  Hence
  the Garland route reduces the operator bound of this claim to a single
  residual: operator-norm control of the degree-2 primitive on the
  CUSP region of `SL_N(Z[1/p])`'s action on the building, where the finite
  link-average is unavailable.  Inside any fixed horoball the stabiliser is
  a (2-step nilpotent)-by-(Levi) group whose Ad-cohomology is controlled by
  its abelian/unipotent part --- amenable, hence op-bounded primitives
  exist there for free --- so the genuine obstruction is the GLUING of the
  cusp primitives to the cocompact-core Garland primitive across the finitely
  many cusp cross-sections, a reduction-theory (Borel--Serre) boundary
  matching problem rather than a spectral one.  This is the sharpest
  statement of what is left, and it is not addressed by the SOS programs
  (which certify the core gap, not the cusp gluing).
- **The cusp gluing re-imports `SL_2`, so high rank does not by itself
  finish it (2026-08-21).**  The rank induction one hopes for --- cusp
  Levi factors are smaller `SL_k(Z[1/p])`, handle them by induction ---
  does NOT bottom out above `SL_2`.  Degree-2 boundary cohomology sees the
  Borel--Serre strata of corank `<= 2` (parabolics with `<= 3` Levi
  blocks); ALREADY the maximal (corank-1) rational parabolic with block
  type `(2, N-2)` has Levi `S(GL_2 x GL_(N-2))`, hence an `SL_2(Z[1/p])`
  factor, for every `N >= 4` (at `N = 4` the type `(2,2)` Levi has TWO
  `SL_2` factors), and its codimension-1 boundary face contributes to
  `H^2`.
  `SL_2(Z[1/p])` is rank one, has the Haagerup property and no property
  `(T)`, so its `H^1`/`H^2` with the restricted Ad-module are NOT gap-
  controlled and the positive local-averaging upgrade is unavailable on
  that stratum --- the exact rank-one difficulty of the `SL_2` Iwahori
  lane (`iwahori-local-global-defect-question`) re-enters at the
  block-`(2,N-2)` cusp face.  So the operator-norm degree-2 primitive for
  `SL_N(Z[1/p])` is not independent of the `SL_2` case; the two horns of
  the flexible-stability residual are LINKED through the cusp geometry, and
  a proof must either control the `SL_2`-Levi primitive directly (the open
  rank-one problem) or exploit that on the `(2,N-2)` stratum the `SL_2`
  factor is coupled to the `GL_(N-2)` block and the unipotent radical in a
  way the isolated `SL_2` lane is not.  This explains structurally why
  raising the rank has not closed the stability input.  The coupling
  exploit one hopes for: the stratum's contribution to degree-2 cohomology
  is `(+)_(i+j=2) H^i(Levi, H^j(U_P, V))`, and `H^j(U_P, V)` decomposes
  (Kostant, algebraic case; Vogan--Zuckerman `(g,K)`-analogue for the
  unitary Ad-module) into Levi representations `F_(mu_w)`,
  `mu_w = w(lambda+rho)-rho`, over `w in W^P` of length `j`; if for
  `j <= 2` NO piece had an `SL_2`-Levi-fixed vector the face would
  contribute nothing there and high rank would close the upgrade.

  **This hope is FALSE for the adjoint probe (computed 2026-08-21).**  For
  `N = 4`, `P` the `(2,2)` maximal parabolic, `V = ad` (`lambda = theta`,
  `theta+rho = (5/2,1/2,-1/2,-5/2)`), `W^P` is the six rearrangements with
  `pos_1 > pos_2` and `pos_3 > pos_4`; an `SL_2`-Levi-fixed vector in
  `F_(mu_w)` occurs iff `(pos_1-pos_2) = 1` (first `SL_2`) or
  `(pos_3-pos_4) = 1` (second).  By length:
  `j=0: (5/2,1/2,-1/2,-5/2)`, gaps `(2,2)`, none;
  `j=1: (5/2,-1/2,1/2,-5/2)`, gaps `(3,3)`, none;
  `j=2: (5/2,-5/2,1/2,-1/2)`, gap `pos_3-pos_4 = 1` -> `mu = (1,-3,1,1)`,
  fixed by the SECOND `SL_2`; and `(1/2,-1/2,5/2,-5/2)`, gap
  `pos_1-pos_2 = 1` -> `mu = (-1,-1,3,-1)`, fixed by the FIRST `SL_2`.
  So `H^2(U_P, ad)` carries exactly two `SL_2`-Levi-fixed classes, one per
  factor.  Hence the coupling does NOT remove the obstruction: those are
  precisely the boundary directions on which the primitive's op-norm is
  governed by `H^*(SL_2(Z[1/p]), .)` with the `SL_2`-Levi acting trivially,
  which is rank-one and not gap-controlled.  The two horns are genuinely
  linked, not apparently: op-norm control on the `(2,N-2)` cusp REQUIRES
  the isolated `SL_2` rank-one input, so this horn does not close ahead of
  the `SL_2` Iwahori lane.  (Caveat: this is the finite-dimensional adjoint
  module; the stability module is the unitary `L^2(M) - inv`, where the
  Vogan--Zuckerman analogue could in principle differ, but the adjoint is
  the natural probe and it already exhibits the fixed classes.)  Next: the
  same computation for the unitary Ad-module via `(g,K)`-cohomology, and
  whether the two fixed classes survive to `H^2` of the total Borel--Serre
  complex or are killed against the interior.
- **Falsification gate.**  An Ad-module 2-cocycle of `SL_N(Z)` with
  `|| c ||_op <= 2`, 2-norm primitive, but no operator-bounded
  primitive would refute this claim; by the route it would have to
  arise from an almost-representation whose Newton correction is
  forced to be operator-large -- a structured non-stability
  phenomenon worth exhibiting in its own right.
