---
rg: 2
id: jnvwy-oracle-marginals-reflect-odd-xor-support-proof
kind: route
title: Identify the oracle PVM with the joint refinement of its two isolated marginals
target: jnvwy-perfect-oracularization-reflects-affine-safety
requires: []
---

Pass a perfect model of the typed oracularized verifier to its faithful
synchronous tracial form.  Fix a sampled seed `z`, put
`x=L^Alice(z)`, `y=L^Bob(z)`, write `O_z^(a,b)` for the oracle PVM, and
write `A_x^a`, `B_y^b` for the two isolated PVMs.  The two
oracle--isolated consistency edges give, by zero rejection and faithfulness,

```text
A_x^a = sum_b O_z^(a,b),       B_y^b = sum_a O_z^(a,b).  (OMP1)
```

Both marginals are coarse-grainings of one PVM, hence commute, and

```text
A_x^a B_y^b = O_z^(a,b).                                  (OMP2)
```

Use `A` and `B` as the source strategy.  The oracle game check makes every
positive atom in `(OMP2)` an accepted source pair, so the strategy is
perfect.  Moreover its positive support at `(x,y)` is exactly the positive
trace support of the oracle PVM.

If this source support were affine-unsafe, choose an odd list
`(a_j,b_j)`, all with `tau(O_z^(a_j,b_j))>0`, whose componentwise xor is
rejected by the source decider.  On the positive oracle self-loop at `z`,
the synchronous joint support contains

```text
((a_j,b_j),(a_j,b_j))
```

for every `j`.  Their odd xor is the diagonal pair labelled by the rejected
source xor.  The oracle game check rejects it, contradicting affine safety
of that self-loop support.  Field-valued answer coordinates are serialized
in the fixed `F_2` basis, so this xor is exactly characteristic-two field
addition.  This proves `(OAR1)` without selecting a canonical completeness
strategy.
