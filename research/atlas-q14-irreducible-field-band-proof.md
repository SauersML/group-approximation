---
rg: 2
id: atlas-q14-irreducible-field-band-proof
kind: route
title: Evaluate every chart word as a Laurent polynomial in one extension-field generator
target: atlas-q14-irreducible-field-bands-pay-quarter-rank
requires:
  - atlas-q14-independent-stratum-has-unbounded-band-width
  - atlas-a4-19243-classical-collapse
---

The diagonal chart conjugator has blocks in `F2[C,C^-1]`, so all fixed
residual blocks are bounded-degree Laurent polynomials in `C`.  They cannot
all vanish formally because specialization at `C=1` is a forbidden classical
packet-collision alignment.  An irreducible companion whose degree exceeds
the fixed polynomial span turns every nonzero residual entry into a nonzero
extension-field scalar, hence an invertible binary `m by m` block.
