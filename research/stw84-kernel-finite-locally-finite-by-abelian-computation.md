---
rg: 2
id: stw84-kernel-finite-locally-finite-by-abelian-computation
kind: claim
title: Kernel-finite locally-finite-by-abelian extensions have dimension equal to quotient rank
---

Let

```text
1 -> L -> G -> A -> 1
```

be an exact sequence of countable groups in which `L` is locally finite and
`A` is abelian.  Suppose that the extension is **kernel-finite on finitely
generated subgroups**:

```text
H intersection L is finite for every finitely generated H subset G.   (KF)
```

Then `G` is amenable and

```text
dim_nuc(C*(G))=dim_Q(Q tensor_Z A).                         (1)
```

The equality includes infinite rational rank.  In particular, this is an
exact computation for nonsplit extensions as well as split ones.

For a semidirect product `G=L rtimes_alpha A`, condition `(KF)` follows from
the concrete finite-orbit-hull hypothesis

```text
<alpha_b(x): b in B, x in E> is finite                    (FOH)
```

for every finite `E subset L` and every finitely generated `B subset A`.
Thus (1) applies to controlled locally-finite-by-abelian semidirect products
with genuinely nontrivial action.
