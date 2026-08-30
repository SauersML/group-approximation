---
rg: 2
id: stw82-af-split-stage-centres-obey-maximum
kind: claim
title: AF split extensions with ideal-central stage centres obey the maximum formula
distinct_from:
  stw82-af-split-centralizer-extensions-obey-maximum: that theorem requires the whole AF section to commute with the ideal; the present theorem requires this only for the centres of one finite-dimensional exhaustion and permits arbitrary matrix-block interaction.
  stw82-central-af-split-extensions-obey-maximum: that theorem has commutative quotient stages and a central section; here the quotient may be UHF and the section need not centralize the ideal.
  stw82-raw-two-cut-reuse-iff-quasidiagonal: that theorem characterizes projectional raw-cut gluing; the present proof removes the extra colour by exact matrix-corner decomposition and assumes no quasidiagonal approximate unit.
artifacts:
  - research/artifacts/stw82-stage-centre-split-audit-2026-08-30.md
---

Consider a unital extension

```text
0 -> I -> E --q--> D -> 0                              (SC1)
```

with a unital *-homomorphic section `s:D->E`.  Suppose the unital AF
algebra `D` has an increasing finite-dimensional exhaustion

```text
D_1 subset D_2 subset ...,
closure(union_n D_n)=D,                                (SC2)
```

such that

```text
[s(Z(D_n)),I]=0                 for every n.            (SC3)
```

Then

```text
dim_nuc(E)=dim_nuc(I)=max(dim_nuc(I),dim_nuc(D)).       (SC4)
```

In particular, `(SC4)` holds for every unital split extension whose
quotient is UHF: choose an exhaustion by full matrix algebras, whose
centres are scalar, so `(SC3)` is automatic.  It also holds for every
unital split extension with simple finite-dimensional quotient.  No
commutation between the matrix part of `s(D_n)` and `I`, no quasidiagonality
of the extension, and no regularity assumption on `I` are required.

The structural reason is exact colour reuse.  Central units of the stage
blocks split `I+s(D_n)` into summands.  Inside a block `M_r`, its lifted
matrix units identify the middle summand with `M_r` over the minimal
unitization of one ideal corner and identify the ideal summand with the
same matrix amplification before unitization.  Matrix amplification and
minimal unitization preserve nuclear dimension, so adjoining the entire
finite-dimensional quotient stage costs no colour.
