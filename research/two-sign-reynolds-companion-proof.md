---
rg: 2
id: two-sign-reynolds-companion-proof
kind: route
title: Split the negative payload atom by a transvection of an auxiliary sign
target: two-sign-reynolds-companion-splits-one-assignment-atom
requires: []
---

Because `J` is independent of `H_a`,

```text
e_(C_a)=e_(H_a)(1+J)/2.
```

Multiplication by the central cut `(1-K)/2` gives `(TRC3)`.  On the
`K=-1` sector, `(TRC2)` sends `J` to `-J`; it fixes `A_a`.  It therefore
conjugates the two orthogonal projections `A_a(1+J)/2` and
`A_a(1-J)/2`.  Tracial invariance proves `(TRC4)`.

For the HNN edge, the subgroup-Hecke identity gives

```text
e_(H_a) t e_(C_a)=t e_(C_a).
```

The extra relation `[t,K]=1` permits multiplication by `(1-K)/2`, so
`qtp=tp`.  Hence `v=tp` is a source-full partial isometry with final
projection below `q`.  Trace cyclicity and `(TRC4)` give

```text
tau(q-vv^*)=tau(q)-tau(v^*v)=tau(q)-tau(p)=tau(A_a)/2.
```

The robust assertion uses only a fixed finite multiplication table, the
dimension-free subgroup-Hecke estimate, and polar decomposition on the
fixed source projection.  Their errors telescope with a constant depending
only on the displayed finite cell.

