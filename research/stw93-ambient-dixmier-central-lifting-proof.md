---
rg: 2
id: stw93-ambient-dixmier-central-lifting-proof
kind: route
title: Convert uniform coordinatewise averaging into ambient self-commutators and identify the centrality failure
target: stw93-central-commutator-lifting-is-trace-hinge
requires:
  - stw93-super-mcduff-tracial-central-quotient
artifacts:
  - research/artifacts/stw93-central-commutator-lifting-audit-2026-08-30.md
---

## Uniform ambient averaging

The algebra `A` is simple, unital, exact, and has a unique trace.  It has the
Dixmier property by the Haagerup--Zsido theorem.  Its Z-stability gives
strict comparison and radius of comparison zero.  The uniform-Dixmier
theorem of Archbold--Robert--Tikuisis therefore gives the following: for
every `epsilon>0` there is an integer `m`, independent of the positive
contraction `a in A`, and unitaries `u_1,...,u_m in A` such that

```text
||m^(-1)sum_j u_j a u_j* - tau(a)1||<epsilon.            (1)
```

For the free-group factor this is the uniform form of Powers averaging; the
point needed below is that `m` is uniform while the unitaries may depend on
`a`.

Let `h=[(h_n)] in I_+` be a contraction.  Apply `(1)` coordinatewise, with
the same `m`, to obtain unitaries `u_(j,n)`.  Put

```text
y_(j,n)=m^(-1/2) h_n^(1/2) u_(j,n)*.
```

Then

```text
sum_j(y_(j,n)y_(j,n)*-y_(j,n)*y_(j,n))
 =h_n-m^(-1)sum_j u_(j,n)h_nu_(j,n)*.                    (2)
```

Because `tau(h_n)->_omega 0`, equations `(1)` and `(2)` approximate `h`
within `epsilon` by a fixed finite sum of self-commutators in `A_omega`.
Letting `epsilon` decrease proves `(ACC1)` for positive elements.  Positive
and negative parts of a self-adjoint element of the ideal `I` remain in
`I`; taking their difference proves `(ACC1)` on `I_sa`.

This also directly shows that `A_omega` has no extra trace on `I`: every
trace vanishes on the right side of `(2)`.  Equivalently, uniform singleton
Dixmier averaging makes the full ultrapower uniquely traced.

## The exact relative criterion

Every bounded trace on `D` vanishes on `Com_sa(D)`.  Hence the right side of
`(ACC2)` makes every normalized trace on `D` vanish on `I`; it then factors
through the II_1 factor `D/I` and is the canonical limit trace.

Conversely, suppose `D` has a unique normalized trace.  The Jordan
decomposition of a bounded self-adjoint tracial functional consists of
positive tracial functionals.  Therefore every bounded tracial functional
on `D` is a scalar multiple of the unique trace.  By the Cuntz--Pedersen
commutator annihilator theorem,

```text
Com_sa(D)={a in D_sa:tau_omega(a)=0}.
```

Every element of `I_sa` has zero limit trace, proving the other direction
of `(ACC2)`.

Finally, a finite self-commutator approximation in `D` can be lifted to
bounded representatives.  Each representative sequence is norm-central,
and the quotient norm is the ultralimit norm, giving `(ACC3)`.  Conversely,
`(ACC3)` defines elements of `D` and gives the corresponding approximation
there.  Thus `(ACC3)` is exactly, not merely necessarily, the inclusion on
the right of `(ACC2)`.

## Why Powers averaging stops

The sequences `(u_(j,n))` selected in `(1)` vary with `h_n`.  Centrality of
`h=[(h_n)]` controls `[h_n,a]` only for each fixed `a in A`; it gives no
control against the moving unitaries `u_(j,n)`.  Consequently

```text
y_j=[(m^(-1/2)h_n^(1/2)u_(j,n)*)]
```

belongs to `A_omega` but need not belong to `D`.  Full-factor spectral gap
only replaces norm-central sequences by scalar/free-factor data in tracial
`2`-norm, whereas `(ACC3)` requires operator-norm centrality of every
commutator factor.  This is the precise promotion which remains open.

**Sources.**  The uniform averaging input is Archbold--Robert--Tikuisis,
*The Dixmier property and tracial states for C*-algebras*, Theorem 3.2,
Lemma 3.9, and Corollary 3.22, arXiv:1611.08263.  The annihilator identity is
Cuntz--Pedersen, *Equivalence and traces on C*-algebras*, Proposition 2.7.
