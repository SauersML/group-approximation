---
rg: 2
id: stw22-screen-local-lifts-with-summable-reciprocals-proof
kind: route
title: Screen increasingly divisible local lifts and sum their reciprocal trace costs
target: stw22-c-space-screening-from-local-lifts
requires:
  - stw22-finite-dimensional-colouring-from-local-lifts
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-c-space-selective-screening-audit-2026-08-30.md
---

Put `R=pi_tau(U)''` and assume `(LWCL)`.  Let `sigma` be a bounded positive trace on a fibre
gap `K_x/J_x`, let `a` be a positive contraction, fix `eta>0`, and set

```text
c=(a-eta)_+.
```

It is enough to prove `sigma(c)=0`.

Fix an arbitrary `epsilon>0` and choose positive integers `m_n` with
`sum_n m_n^(-1)<epsilon`.  Since `a(x)=0` in `2`-norm, Chebyshev gives, for
every `n`, a neighbourhood `W_n` of `x` on which

```text
tau(supp(c(t))) < 1/(2m_n).                              (CSP1)
```

Choose a closed neighbourhood `F_n` of `x` contained in `W_n`.  On `W_n`,
the local weighted-lifting lemma from
`stw22-colour-local-weighted-corner-lifts-proof` gives an open cover by
domains on which `c` has weighted lifts into each of `m_n` fixed pairwise
orthogonal projections of trace `1/m_n`.  Together with the discard set
`X\F_n`, these domains form an open cover `U_n` of `X`.

Apply property `C` to `(U_n)`.  We obtain pairwise disjoint families `V_n`
refining `U_n`, whose union covers `X`.  Compactness gives a finite
subcover drawn from finitely many of the families.  Discard every selected
set which refines `X\F_n`.  The remaining selected sets still have open
union containing `x`, because no discard set contains `x`.  After shrinking
to a smaller neighbourhood of `x`, they give a finite cover entirely by
local weighted-lift domains.

Choose a central partition of unity `(f_beta)` which sums to one on a
neighbourhood of `x` and is subordinate to these remaining sets.  Terms
away from that neighbourhood lie in `J_x` and are irrelevant.  Group the
functions according to their family and put

```text
g_n=sum_(beta in V_n) f_beta.
```

For every selected `n` and `1<=j<=m_n`, define

```text
v_(j,n)=sum_(beta in V_n) f_beta^(1/2) w_(j,beta),        (CSP2)
```

where `w_(j,beta)` is the local weighted lift into the `j`-th fixed corner.
The sets in `V_n` are pairwise disjoint, so all cross terms in `(CSP2)`
vanish.  Hence

```text
v_(j,n)^*v_(j,n)=g_n c.
```

For fixed `n`, the range elements for different `j` lie in orthogonal
corners and their sum is contractive.  Traciality gives

```text
m_n sigma(g_n c)
 =sigma(sum_(j=1)^m_n v_(j,n)v_(j,n)^*)
 <=||sigma||.                                            (CSP3)
```

The finitely many selected `g_n` sum to one in the germ at `x`.  Therefore

```text
sigma(c)
 =sum_n sigma(g_n c)
 <=||sigma|| sum_n 1/m_n
 <epsilon||sigma||.
```

Since `epsilon` was arbitrary, `sigma(c)=0`.  Letting `eta` decrease to
zero proves `sigma(a)=0`.  Thus every fibre gap is bounded-trace-free, and
the abstract fibre-gap criterion gives the asserted description of all
traces on `M`.

After `(LWCL)`, the proof uses exactly one topological operation: selectively screening the
sequence of local weighted-lift covers into disjoint families.  A failure
of property `C` blocks this summable-colour argument, but is not by itself a
construction of a singular trace.
