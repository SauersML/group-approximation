---
rg: 2
id: one-marginal-free-phase-escape-proof
kind: route
title: Conjugate a same-sign Hadamard plane by independent free phases
target: one-binary-marginal-block-escape
requires: []
---

Because the free generators commute with `C[K]` in the direct product and
the `e_i` are orthogonal,

```text
W^*W=sum_(i,j)e_i h_i^(-1)h_j e_j=sum_i e_i=q,
WW^*=q.                                                    (OBM5)
```

The same diagonal calculation gives `Wd=dW`.  Equations `(OBM2)` and
`(OBM5)` show that the `P_i` are an orthogonal projection partition and

```text
sum_i epsilon_i P_i=W u d u^* W^*=WdW^*=d.
```

On the Hadamard plane,

```text
f_r=(E_rr+E_ss+E_rs+E_sr)/2,
f_s=(E_rr+E_ss-E_rs-E_sr)/2.                              (OBM6)
```

Consequently the coefficient of `h_r h_s^(-1)` in `P_r` is `E_rs/2`, and
the corresponding coefficient in `P_s` is `-E_rs/2`.  Matrix units are
nonzero, and distinct reduced words of `F_D` are linearly independent in its
group algebra.  Neither projection belongs to `qC[K]q tensor 1`.

If the coarse assignment blocks containing `r` and `s` are distinct, summing
the refined projections within either block cannot cancel its cross term: the
only Hadamard cross terms join `r` to `s`, and the other endpoint lies outside
that coarse sum.  If both endpoints belong to one assignment block, their sum
on the Hadamard plane is `E_rr+E_ss`, which the diagonal free phases fix.

If both sign fibers of `d` are singletons, duplicate the whole coordinate
model.  If one fiber is empty, `d` is scalar and any pair may be used.  This
preserves all normalized rational atom weights while ensuring the required
two-dimensional plane, but it does not manufacture distinct assignments in
one sign fiber.
