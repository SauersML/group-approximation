---
rg: 2
id: nonhyperlinear-from-wedderburn-hall-deficit
kind: route
title: A relator-forced weighted Fourier Hall deficit forbids finite atlas microstates
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - weighted-unitary-hall-deficit-gap
  - atlas-wedderburn-hall-deficient-support-certificate
---

Assume the prerequisites and a hyperlinear regular-atlas sequence.  Apply the
Hall certificate to its fixed regular `A_8` Fourier decomposition.  The source
set `S` and its allowed target neighborhood have a fixed capacity deficit
`gamma>0`.  Therefore `weighted-unitary-hall-deficit-gap` gives

```text
sum_(v in S, u notin N(S)) ||p_u U_n p_v||_2^2
 >= gamma                                                     (NWH1)
```

for every relative chart unitary `U_n`.

The certificate simultaneously says that the full atlas packet drives the
same forbidden-block energy to zero as its relator defect tends to zero.  This
contradicts `(NWH1)`.  Hence the regular-atlas microstate sequence from the
hyperlinearity criterion cannot exist and the explicit binary Leavitt unit
group is nonhyperlinear.

This creates a one-hole direct portfolio whose remaining theorem is finite and
combinatorial after Fourier compilation: derive enough coefficient block zeros
from the actual packet to make one weighted min-cut deficient.