---
rg: 2
id: labeled-overlap-polar-decomposition-proof
kind: route
title: Take the polar decomposition of the diagonal overlap operator
target: pvm-overlap-polar-matches-large-labeled-carriers
requires: []
---

Put `A=sum_v E_vF_v`.  Then `E_vA=AF_v`, so every polar component respects
the labels.  Orthogonality gives

```text
||A||_2^2=sum_vtau(F_vE_v)=1-Gamma,
tau(A)=sum_vtau(E_vF_v)=1-Gamma,
||A-I||_2^2=Gamma.                                      (POP1)
```

If `A=V|A|` is the polar decomposition, then

```text
||V-A||_2^2=tau((1-|A|)^2)<=tau(1-|A|^2)=Gamma          (POP2)
```

on its initial support, and the kernel projections on both sides have trace
at most `Gamma`.  This proves `(POM2)--(POM3)`.  The difference of the
individual labeled ranks is bounded by the off-row plus off-column overlap;
summing gives total variation at most `2Gamma`.  Remove those excess pieces,
match the equal-rank complements, and extend `V`.  The triangle inequality
from `(POP1)--(POP2)` plus at most `2Gamma` support for the extension gives
the safe constant in `(POM4)`.
