---
rg: 2
id: deligne-sector-gap-equivalence-proof
kind: route
title: Tensor a surviving Maslov sector with canonical quotient microstates, and cut any extension microstate back into sectors
target: deligne-sector-gap-is-exactly-nonhyperlinearity
requires:
  - finite-central-hs-sector-decomposition
  - maslov-inverse-sector-symmetry
artifacts:
  - research/artifacts/deligne-sector-tensor-camouflage-2026-08-21.md
---

The quotient `Gamma=Sp_4(Z)` is residually finite, hence has
finite-dimensional canonical-character microstates.  Given any sequence of
`alpha`-projective almost representations `U_n` of `Gamma`, tensor it with
such a sequence `V_n` and put

```text
rho_n(z)=omega I,
rho_n(s)=U_n(s) tensor V_n(s)
```

on lifted presentation generators.  Projective phases in `U_n` reproduce
the central powers of `z`; the ordinary defects of `V_n` tend to zero, so
`rho_n` satisfies the presentation of `E_3` asymptotically.  For
`e=z^k g`, if `g!=1` in `Gamma`, the trace of `rho_n(e)` tends to zero because
the `V_n(g)` factor has canonical trace.  If `g=1` and `e!=1`, then
`rho_n(e)=omega^k I!=I`.  The induced metric-ultraproduct homomorphism is
therefore injective.  Thus one surviving nontrivial projective sector already
makes `E_3` hyperlinear.

Conversely, a faithful hyperlinear embedding of `E_3`, represented by finite
presentation microstates, cannot send `z` to the identity.  Rounding the
order-three central word and applying
`finite-central-hs-sector-decomposition` leaves positive ultraproduct trace
in at least one nontrivial central-character block.  On that block one gets
an `alpha`- or `alpha^2`-projective almost representation with vanishing
defect.  `maslov-inverse-sector-symmetry` exchanges the two sectors.  Hence
`E_3` is hyperlinear if and only if either, equivalently both, nontrivial
sector defect infima are zero.

The same cutting argument shows that failure of one-word collapse produces a
positive-density nontrivial sector.  Tensor camouflage then makes `E_3`
hyperlinear.  The reverse implication is immediate from faithful extension
microstates, which keep `z` separated.  This proves all four equivalences.

