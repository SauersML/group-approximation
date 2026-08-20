---
rg: 2
id: piecewise-group-transport-gives-corner-unitaries
kind: claim
title: Finite piecewise group transport produces exact algebraic corner unitaries and involutions
artifacts:
  - research/artifacts/signed-hecke-direct-trace-promotion-2026-08-20.md
---

Let `q in C[Gamma]` be a projection. Let `(p_i)_(i in I)` and
`(r_i)_(i in I)` be finite orthogonal partitions of `q` by algebraic
projections, and suppose `g_i in Gamma` satisfy

```text
g_i p_i g_i^(-1)=r_i.                                  (PGT1)
```

Put `v_i=g_i p_i=r_i g_i` and `V=sum_i v_i`. Then each `v_i` lies in
`qC[Gamma]q`, and

```text
v_i^*v_j=delta_(ij)p_i,       v_i v_j^*=delta_(ij)r_i.  (PGT2)
```

Consequently `V^*V=q=VV^*`: `V` is a unitary relative to the corner unit.

If an involution `s:I->I` also satisfies

```text
p_(s(i))=r_i,                 g_(s(i))=g_i^(-1),        (PGT3)
```

then `v_(s(i))=v_i^*`, so `V=V^*` and `V^2=q`.

The first genuinely nonnormal example has two pieces. If `q=p_0+p_1` and
`g p_0 g^(-1)=p_1`, then

```text
V=g p_0+g^(-1)p_1                                    (PGT4)
```

is a self-adjoint corner involution, even though `g` need not stabilize `q`.
Thus multi-double-coset support is not merely a way around the single-piece
stabilizer obstruction; two pieces already suffice algebraically.
