---
rg: 2
id: packet-natural-selectors-cannot-extract-one-bounded-copy
kind: claim
title: A packet-natural selector cannot extract one bounded irreducible copy from arbitrary multiplicity
distinct_from:
  subhomogeneous-energetic-carriers-cannot-have-a-strict-regular-gap: that rules out bounding every irreducible of the energetic carrier; this rules out a canonical bounded-copy selection even when the fixed packet irreducible itself has small dimension.
  finite-normalizer-star-no-go: that uses the regular marked sector to refute one swap-star geometry; this is the multiplicity-symmetry obstruction for every packet-local reducing projection.
  fixed-packet-orbits-cannot-amplify-a-gram-line: that shows a bounded packet orbit cannot turn one adjoint vector into positive density; this shows the dual failure, that packet data cannot choose one bounded summand out of a large multiplicity space.
  bounded-output-energetic-decoder-gives-the-canonical-ceiling: that is the positive compactness theorem once bounded output has been supplied; this proves that the output cannot be selected naturally from a fixed packet alone.
---

Let `rho:K->U(r)` be an irreducible representation of a finite group and put

```text
pi_m=rho tensor I_m.
```

Suppose a rule depending only on the represented packet assigns a reducing
projection `P_m` to `pi_m` and is natural under unitary equivalence.  In
particular, every multiplicity unitary `I_r tensor W`, `W in U(m)`, is an
automorphism of the represented packet and therefore

```text
(I_r tensor W)P_m(I_r tensor W)^*=P_m.                  (PNS1)
```

Then

```text
P_m=0  or  P_m=I_(rm).                                  (PNS2)
```

Consequently no nonzero packet-natural selection has rank bounded
independently of multiplicity.  The result also applies after replacing
`rho(K)` by any fixed finite packet/normalizer representation and then taking
common amplifications.

Thus the bounded-output decoder needed by reverse Kleene cannot be a spectral
projection, central idempotent, Reynolds operator, or other unitary-natural
function of one fixed packet table.  It must use outside matrices to break
the full multiplicity-unitary symmetry, and it must do so in a
canonical-profile-dependent way not equivalent to making the whole orbit
corner subhomogeneous.

