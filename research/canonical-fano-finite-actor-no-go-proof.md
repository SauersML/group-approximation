---
rg: 2
id: canonical-fano-finite-actor-no-go-proof
kind: route
title: Compute the free Fano commutator and extend its canonical type through every finite actor
target: canonical-fano-free-product-defeats-finite-actor-payment
requires:
  - rstar-fano-caps-have-seven-maximal-parity-covers
  - canonical-types-extend-every-finite-bass-serre-actor
---

Fourier inversion in `C[C_2^3]` gives `(CFP1)`.  Free-product normal form
then gives `(CFP3)--(CFP4)` exactly; the artifact independently reduces every
group-algebra word over the rationals and prints

```text
group=C2^3*C2
cap_characters=4
q=(1-a_111)/2
canonical_trace_q=1/2
canonical_trace_tqtq=1/4
canonical_commutator_hs2=1/2
```

The base is a free product of finite groups and hence virtually free and
residually finite, so its canonical trace has matrix microstates.  Apply the
second required claim to any finite Bass--Serre actor.  It supplies an exact
extension of the same canonical base representation.  All proposed actor
rows therefore have zero defect while the explicitly computed base
commutator retains squared norm `1/2`, contradicting `(CFP5)`.

