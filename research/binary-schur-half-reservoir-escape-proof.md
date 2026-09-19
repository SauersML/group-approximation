---
rg: 2
id: binary-schur-half-reservoir-escape-proof
kind: route
title: Split the multiplicity evenly between the two diagonal target blocks
target: binary-schur-canonical-weights-have-half-reservoir-escape
requires:
  - binary-schur-child-toeplitz-self-embedding
---

Let `V_x` be the complex unitary full-packet type belonging to the selected
sector, and let `W_+,W_-` be the natural types of the two target simple
blocks.  The module statement `(BST3)` says

```text
Res_phi(W_+)=V_x=Res_phi(W_-).                           (0)
```

Let

```text
H=V_x tensor C^m
  =H_+ direct_sum H_-,
H_+=W_+ tensor C^(m/2),
H_-=W_- tensor C^(m/2).                                 (1)
```

The parent packet representation is

```text
pi_parent(g)=V_x(g) tensor I_m.                         (2)
```

Represent the two target simple summands with multiplicities `m/2,m/2`.
By `(0)`, restriction along `phi` gives

```text
Res_phi(pi_child)
 =(V_x tensor I_(m/2)) direct_sum
  (V_x tensor I_(m/2))
 ~=V_x tensor I_m=pi_parent.                            (3)
```

Thus the complete old-packet characters, hence all old-packet word moments,
agree exactly.  The two central projections of the target algebra are the
projections `Q_+,Q_-` onto `H_+,H_-`, so

```text
tr_H(Q_+)=tr_H(Q_-)=1/2.                                (5)
```

These are precisely the balanced corrected-child weights.  This argument is
representation-theoretic; the splitting-field matrix notation in `(BCW1)`
records the multiplicity rule, while the actual packet matrices are the
complex unitary finite-group representations just used.

Let `S:H_+->H` be inclusion and `T=S^*` projection.  Then

```text
TS=1_(H_+),                ST=Q_+,                      (6)
```

and the unpaid complement `Q_-` has trace `1/2`.  All packet actions reduce
the displayed decomposition, so `(6)` is compatible with every recovered
packet type and adds no packet-character defect.  Taking direct sums over
selector sectors proves the global statement.
