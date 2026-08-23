---
rg: 2
id: bcv-halt-readable-finite-orbit-does-not-transfer-to-gap-irs
kind: claim
title: BCV finite readable orbits live on the HALT branch and do not transfer to the perfect gap IRS
artifacts:
  - research/artifacts/bcv-halt-readable-orbit-audit-2026-08-23.md
distinct_from:
  perfect-zpc-irs-quantum-gap-game: that diagonal argument extracts a perfect IRS strategy on a non-halting soundness instance; this audits the finite completeness strategies in the underlying BCV construction and proves that their finite-orbit geometry is on the opposite branch.
  finite-depth-readable-groupoid-closes-iff-full-orbit-is-finite: that is a universal criterion for monomial closure; this identifies exactly what the concrete BCV completeness construction does and does not supply.
  zpc-readable-control-freezing-to-lcs: that asks for an invariant positive readable fiber in the perfect gap IRS; this proves neither existence nor nonexistence of such a fiber there, but rules out importing it from BCV perfect completeness.
---

For the Bowen--Chapman--Vidick TailoredMIP compiler `M -> G_M`, every
HALT-side perfect ZPC strategy has a finite orbit of its readable Boolean
algebra under all unreadable generators.  Indeed it is a signed-permutation
strategy on a finite signed set, so the image of the whole generated group is
finite and the orbit of every finite-dimensional subalgebra is finite.

This observation does **not** apply to the perfect ZPC-IRS gap strategy in
`perfect-zpc-irs-quantum-gap-game`.  The diagonal proof there necessarily
chooses a non-halting machine `M_0`: BCV soundness gives

```text
omega*(G_(M_0)) < 1/2,
```

while compactness of the restricted IRS space supplies an infinite measurable
ZPC strategy of value one.  It is not a limit of the HALT-side finite
completeness construction, and the pseudo-IRS upper hierarchy records only
fixed cylinder equations, not a uniform bound on readable translate-orbit
size.  Thus the BCV theorem supplies no finite-orbit conclusion for this
`M_0` strategy.

The stronger fixed-fiber shortcut already fails in BCV's canonical question
reduction completeness strategy.  On

```text
C^(F_2^k) tensor C^m,
```

the readable `SamZ` atoms are

```text
E_z = |z><z| tensor I_m,
```

whereas the Pauli-X variables are unreadable and satisfy

```text
(X^alpha tensor I_m) E_z (X^alpha tensor I_m)^*
    = E_(z+alpha).                                      (BCV1)
```

For `alpha != 0`, the two atoms on the right and left are orthogonal.  Hence a
projection `p <= E_z` invariant under every unreadable Pauli-X translation
must satisfy `p <= E_z E_(z+alpha)=0`.  In particular no nonzero joint
readable-assignment atom refining `SamZ` is invariant under all unreadable
generators in this canonical strategy.

Consequently the BCV construction gives exactly one of the two desired
properties on its HALT branch--finite orbit, not an invariant atom--and gives
neither property for the NONHALT perfect-gap IRS selected by the undecidability
argument.  Closing `zpc-readable-control-freezing-to-lcs` still requires a new
theorem about that maximizing IRS itself: either a uniformly bounded finite
readable orbit, or a positive invariant readable fiber.
