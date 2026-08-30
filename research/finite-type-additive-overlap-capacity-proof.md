---
rg: 2
id: finite-type-additive-overlap-capacity-proof
kind: route
title: Bound each restriction multiplicity and compress the additive defect to orthogonal atoms
target: finite-type-additive-overlap-obeys-row-column-capacity
requires:
  - finite-type-restriction-overlap-defect-formula
---

Let

```text
m_ij=<Res_(L_ij) rho_i^(g_i),Res_(L_ij) sigma_j^(h_j)>.
```

The intertwiner space counted by `m_ij` is contained in the full space of
linear maps between vector spaces of dimensions `d_i,e_j`, so

```text
m_ij<=d_i e_j.                                           (ARC6)
```

The exact restriction-overlap formula therefore gives

```text
tau(p_i r_j)
 <=d_i^2 e_j^2 |L_ij|/(|H_i||K_j|)
 =tau(p_i) e_j^2/[B_j:L_ij].                             (ARC7)
```

Since `Pp_i=p_i`,

```text
(P-R)p_i=(1-R)p_i.
```

Positivity and traciality give

```text
||(1-R)p_i||_2^2
 =tau(p_i)-tau(p_iR)
 =tau(p_i)-sum_j tau(p_i r_j).                           (ARC8)
```

Substitution of `(ARC7)` gives the positive part of the row bound for each
`i`. The vectors `(P-R)p_i` are pairwise `L2`-orthogonal: for
`i!=k`, traciality moves the terminal `p_i` next to `p_k` in their
inner product. Moreover, right multiplication by `P` is contractive.
Therefore

```text
||P-R||_2^2 >= ||(P-R)P||_2^2
             =sum_i ||(P-R)p_i||_2^2,
```

and summing the positive row bounds proves the first inequality in
`(ARC3)`. Interchanging the two families proves the column inequality.

If `P=R`, the left side of `(ARC3)` is zero, proving `(ARC4)`. If
additionally `C_i=1`, equality in `(ARC8)` forces equality in every
nonnegative estimate `(ARC7)`. Hence `m_ij=d_i e_j` whenever the cross
capacity is used. Every linear map between the two restriction spaces is
then equivariant, which forces both restricted actions to be the same scalar
character. This proves the rigidity statement.
