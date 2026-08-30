---
rg: 2
title: STW LXXXII quasicentral support-thickening audit (2026-08-30)
kind: artifact
---

# Result

Let `p in M(A)` and `L=closure(ApA)` for separable `A`.  If `L` has a
projectional approximate unit quasicentral in `A` and asymptotically
commuting with `p`, then

```text
dim_nuc(A+C p)=dim_nuc(A).
```

This is the first multiplier-support result here allowing `L` to be proper
and essential, hence genuinely noncomplemented.

# Spectral-repair audit

For a projection `e_n`, its `p`-block diagonal part

```text
d_n=pe_np+(1-p)e_n(1-p)
```

commutes with `p` and converges in norm to `e_n` because the off-diagonal
corners are measured by `[e_n,p]`.  Hence `d_n` is asymptotically
idempotent.  Cutting its spectrum at `1/2` produces a projection `r_n in L`
which commutes with `p` and satisfies `norm(r_n-e_n)->0`.  Membership in `L`
is exact: the cutoff is continuous on `Spec(d_n)` and vanishes at zero.

The projections

```text
q_n=p+(1-p)r_n in L+C p
```

form an approximate unit for `L+C p`.  For `a in A`, both `pa` and `ap`
belong to `L`, and the exact commutator identity

```text
[q_n,a]=(1-p)[r_n,a]+[p,a](1-r_n)
```

proves quasicentrality.  They commute with `p` exactly.  Thus the residual
extension by `A/L` is quasidiagonal, not merely asymptotically split or
quasidiagonal modulo an uncontrolled corner.

# Dimension audit

The quasidiagonal-extension maximum theorem gives the maximum of the
dimensions of `J=L+C p` and `A/L`.  The projection `p` is full on `L`, so
the existing full-corner theorem gives `dim_nuc(J)=dim_nuc(L)`.  Both `L`
and `A/L` have nuclear dimension at most that of `A`; because `A` is an
ideal of `A+C p`, equality follows.  No instance of the unknown arbitrary
extension formula is used.

# Noncomplemented test

For

```text
A=((K(H)~) tensor K(H)) tensor C([0,1]),
p=e_11 tensor 1 tensor 1,
```

the generated ideal is

```text
L=(K(H) tensor K(H)) tensor C([0,1]).
```

It is proper and essential, so it cannot be complemented.  Finite-rank
tensor projections give the required quasicentral approximate unit and
commute with `p`.  The quotient by `L` is
`K(H) tensor C([0,1])`, forcing `dim_nuc(A)=1`; the theorem therefore gives
an explicit noncomplemented dimension-one instance.

# Remaining boundary

The criterion does not cover a generated ideal lacking projectional
quasicentral cuts relative to `p`.  In particular, it does not reorganize
the transition band of a nonquasidiagonal residual extension.  That is the
next genuinely nonprojectional part of the multiplier-projection problem.
