---
rg: 2
id: stw82-exact-reducing-tail-splitting-proof
kind: route
title: Split an internal compression from an exactly reducing multiplier tail
target: stw82-internally-reduced-projection-exhaustions
requires:
  - stw82-stabilized-coefficient-projections
artifacts:
  - research/artifacts/stw82-internally-reduced-projection-exhaustion-audit-2026-08-30.md
---

Set

```text
A_n=Q_n A Q_n,       p_n=pQ_n,       r_n=p(1-Q_n).
```

Because `p` commutes with `Q_n`, both `p_n` and `r_n` are projections and
are orthogonal.  The assumption `pQ_n in A` and the identity
`Q_np_nQ_n=p_n` put `p_n` in `A_n`.  If `a in A_n`, then `a=Q_naQ_n`, so

```text
r_na=p(1-Q_n)Q_naQ_n=0,
ar_n=Q_naQ_n(1-Q_n)p=0.                                (ERT1)
```

It follows that

```text
E_n=C*(A_n,p)=A_n+C r_n.                                (ERT2)
```

If `r_n` is nonzero, the two summands in `(ERT2)` are orthogonal and the
map `A_n direct_sum C -> E_n`, `(a,lambda) |-> a+lambda r_n`, is an
isomorphism.  If `r_n=0`, then `E_n=A_n`.  In either case,

```text
dim_nuc(E_n)<=max(dim_nuc(A_n),0)<=dim_nuc(A),          (ERT3)
```

where the scalar entry is omitted when `r_n=0`.  The inequality is
hereditary permanence; if `A=0`, then `M(A)=0` and the theorem is trivial.

Nestedness does not require constant block increments.  Since the `Q_n`
are increasing and commute with `p`, the difference
`D_n=Q_(n+1)-Q_n` is a projection commuting with `p`, and

```text
pD_n=pQ_(n+1)-pQ_n in A,
Q_(n+1)(pD_n)Q_(n+1)=pD_n.
```

Thus `pD_n in A_(n+1)` and

```text
r_n=r_(n+1)+pD_n in E_(n+1).                            (ERT4)
```

Also `A_n subset A_(n+1)`, so `(ERT4)` proves `E_n subset E_(n+1)`.

Strict convergence `Q_n->1` gives `Q_naQ_n->a` in norm for every `a in A`.
Hence `closure(union_n A_n)=A`.  Every `E_n` contains `p=p_n+r_n`, and
therefore

```text
closure(union_n E_n)=A+C p.                             (ERT5)
```

Inductive-limit permanence and `(ERT3)` imply
`dim_nuc(A+C p)<=dim_nuc(A)`.  Conversely, `A` is an ideal of `A+C p`, so
ideal permanence gives the reverse inequality.  This proves `(IRE2)`, also
when the common value is infinite.

For the block-module specialization, let `R_n` be the projection onto
`H_1 direct_sum ... direct_sum H_n` and put `Q_n=1_B tensor R_n`.  The
strict block sum `p=direct-sum_j e_j` commutes with every `Q_n`, and

```text
pQ_n=e_1 direct_sum ... direct_sum e_n
    in B tensor K(H).
```

Thus `(IRE1)` holds.  No relation between consecutive block sizes or
Murray--von Neumann classes is used; `(ERT4)` is precisely the nestedness
check for arbitrary increments.
