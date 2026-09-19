---
rg: 2
id: uniform-central-sign-gap-proof
kind: route
title: Exactify the canonical negative sign corner and renormalize its defects
target: uniform-central-sign-gap-implies-nonhyperlinear
requires:
  - central-involution-corner-exactification
---

Assume `Gamma` hyperlinear and choose canonical-trace microstates.  Apply
`central-involution-corner-exactification` to obtain an exact central
involution `Z_n` and corrected generators, all at `o(1)` normalized-HS
distance from the originals.  Put `e_n=(1-Z_n)/2`.  Since `J!=1`, canonical
trace gives

```text
tau_n(e_n)=(1-tau_n(Z_n))/2 ->1/2.
```

Restrict each corrected generator to `e_n`.  Centrality makes this restriction
unitary and sends `J` to `-e_n`.  For every fixed relator defect `D_n`,

```text
||e_n D_n e_n||_(2,e_n)
 <=tau_n(e_n)^(-1/2)||D_n||_(2,n)=o(1).
```

Thus the restricted tuple satisfies `(UCG2)` for all sufficiently large `n`,
a contradiction.

