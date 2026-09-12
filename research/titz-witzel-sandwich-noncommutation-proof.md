---
rg: 2
id: titz-witzel-sandwich-noncommutation-proof
kind: route
title: Square the sandwich and remove the two copies of its commutator defect
target: titz-witzel-sandwich-matchings-need-macroscopic-noncommutation
requires:
  - titz-witzel-two-generator-involution-sandwich-normal-form
---

Put `q=pup`.  The sandwich defect is

```text
eta_J=d(qc,1)=d(q,c^(-1)).                                (1)
```

Squaring costs at most twice the distance in (1), while inversion preserves
distance, so

```text
d(q^2,1)
 <= d(q^2,c^(-2))+d(c^(-2),1)
 <= 2 eta_J+delta_c.                                      (2)
```

Now expand

```text
q^2=p u p^2 u p.                                          (3)
```

Replacing the middle `p^2` by the identity costs exactly at most `theta`.
This changes (3) to `p u^2p`.  Bi-invariance gives

```text
d(pu^2p,1)=d(u^2,p^(-2)),                                 (4)
```

and `d(p^(-2),1)=theta`.  The triangle inequality applied to (2)--(4)
therefore gives

```text
d(u^2,1)<=delta_c+2eta_J+2theta.
```

The fixed-word telescoping inequality yields
`d(u^8,1)=d((u^2)^4,1)<=4d(u^2,1)`, proving `(TWSN3)`.  Since `beta` and
`a` are involutions,

```text
p^2=beta a beta a=[beta,a],
```

for the commutator convention `[g,h]=ghg^(-1)h^(-1)`.  Taking limsups in
`(TWSN3)` proves `(TWSN4)`.  Finally

```text
d(p^2,1)<=2d(p,1)=2d(beta,a),
```

so `(TWSN4)` also proves `(TWSN5)`.  The alternating-component
interpretation is the usual degree-at-most-two graph obtained by drawing
the `a`- and `beta`-edges: `p=beta a` walks two colored edges at a time, and
`p^2` moves exactly the points whose `p`-orbit has length not dividing two.

The shared dependency-free checker evaluates both inequalities on random
finite permutation instances in addition to checking the normal-form
identities.
