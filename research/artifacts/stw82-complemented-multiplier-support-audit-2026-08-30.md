---
rg: 2
title: STW LXXXII complemented multiplier-support audit (2026-08-30)
kind: artifact
---

# Result

For a sigma-unital C*-algebra `A` and `p in M(A)` a projection, put
`L=closure(ApA)`.  If `L` is a complemented ideal of `A`, then

```text
dim_nuc(A+C p)=dim_nuc(A).
```

Equivalently, this applies when the generated ideal has a central multiplier
support projection.  The multiplier projection itself need not be central
or full in `A`.

# Proof audit

If `A=L direct_sum B` and `b in B`, then `bpb^*` lies both in `L`, by the
definition of the generated ideal, and in `B`, by ideality.  Thus `bpb^*=0`,
which forces `bp=0`; adjoints give `pb=0`.  It follows simultaneously that

```text
L=closure(LpL)
```

and that

```text
A+C p=(L+C p) direct_sum B.
```

The first identity makes `p` full as a multiplier of `L`.  Complementation
passes sigma-unitality from `A` to `L`, so the already proved full-support
corner argument gives

```text
dim_nuc(L+C p)=dim_nuc(L).
```

Taking the maximum across the displayed direct sum proves the theorem.
Every algebraic use of complementation is explicit; no instance of the
unknown extension maximum formula is imported.

# Strictness check

For

```text
A=(K(H) tensor M_2) direct_sum C_0((0,1)),
p=(1_(B(H)) tensor e_11,0),
```

the generated ideal is the first summand.  The second summand proves that
`p` is nonfull, while the `M_2` matrix units prove that `p` is noncentral.
Thus the theorem is strictly beyond both the full-projection and
central-projection cases.

# Remaining boundary

For a general nonfull projection, `L+C p` is still computed by the full
corner argument and the residual quotient is `A/L`.  The present theorem
closes this residual gluing exactly when `L` is a direct summand.  Any
counterexample to multiplier-projection invariance must therefore have a
proper, noncomplemented generated ideal; equivalently, its support is not a
central projection of `M(A)`.
