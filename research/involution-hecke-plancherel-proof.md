---
rg: 2
id: involution-hecke-plancherel-proof
kind: route
title: Compute the identity coefficient of one compressed group element
target: involution-hecke-corner-has-no-proper-literal-projections
requires:
  - mipstar-bcs-tracial-nonru-exists
---

Traciality and `q^2=q` give `tau(qgq)=tau(gq)`.  Expanding
`gq=(g+gh)/2`, the canonical trace extracts the identity coefficient and
gives `(IHC4)`.  A projection of trace zero in a finite von Neumann algebra
with faithful trace is zero.  If `g=e` or `g=h`, direct multiplication gives
`qgq=q`.  This proves `(IHC3)`.

If all BCS variable projections have this form, evaluation `p_x=0` or `q`
is a scalar model in the corner.  Every defining polynomial already
vanishes, so the corresponding bits form a classical solution.  This is an
`R^U` model, contradicting `mipstar-bcs-tracial-nonru-exists`.

