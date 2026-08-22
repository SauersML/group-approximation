---
rg: 2
id: rstar-fano-caps-have-seven-maximal-parity-covers
kind: claim
title: Seven nonzero parity characters are the maximal Fano-cap cover menu
distinct_from:
  rstar-fano-ghost-affine-hull-criterion: that identifies affine safety with avoiding Fano lines; this classifies every safe support by one of seven maximal caps and compresses the branch menu.
  culf-mastel-rstar-uniform-fano-cap-profile: that conditionally selects and combines context profiles; this reduces its local choices to seven explicit parity rows without proving that a suitable model exists.
  edgeful-or3-four-cap-walsh-packet: that selects four caps with balanced multiplicity for a signed-Hecke packet; this classifies all seven maximal caps without choosing packet weights.
---

**ESTABLISHED.**  Translate the ghost in `R_*` and write the honest points as
`V\{0}`, where `V=F_2^3`.  For every nonzero `lambda in V^*`, put

```text
C_lambda={v in V : lambda(v)=1}.                        (FMC1)
```

Then `C_lambda` is a four-point Fano cap, and every Fano cap is contained in
some `C_lambda`.  Consequently

```text
S is a Fano cap
iff S subseteq C_lambda for some nonzero lambda.         (FMC2)
```

There are exactly seven maximal caps.  In logical coordinates
`t=(x_2,x_3,x_4)`, selecting one is the single extra affine row

```text
a_2 x_2+a_3 x_3+a_4 x_4=1,
(a_2,a_3,a_4) != 0.                                    (FMC3)
```

Together with `x_1+x_2+x_3+x_4=1`, this row excludes the unique ghost.
Therefore an `m`-context cap-profile compiler needs only `7^m` branches,
not all sixty-four local caps.
