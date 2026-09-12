---
rg: 2
id: cap-ranged-common-source-covariance-firewall-proof
kind: route
title: Pull excluded cap atoms through the common source and use factorial trace rigidity
target: full-support-factor-forbids-cap-ranged-common-source-covariance
requires: []
---

Fix a context `c`.  From the covariance row and its adjoint,

```text
A_(c,x)S_c=S_cB_x,
S_c^*A_(c,x)=B_xS_c^*.                                 (FCF1)
```

Using `S_c^*S_c=Q` gives

```text
QB_x=S_c^*A_(c,x)S_c=B_xQ.                             (FCF2)
```

Every variable occurs in a context, so `(FCF2)` puts `Q` in `M' intersect
N`.

Let `E_M:N->M` be the trace-preserving conditional expectation.  By
bimodularity and `(FCF2)`, `E_M(Q)` commutes with every generator of `M`.
Factoriality therefore gives

```text
E_M(Q)=Tr(Q)1.                                          (FCF3)
```

Here `Tr(Q)>0` because the trace is faithful and `Q!=0`.  Equivalently, the
normalized compression trace satisfies

```text
Tr(Qb)/Tr(Q)=tau(b)                 (b in M).           (FCF4)
```

Now choose `a notin K_c`.  Since the joint atoms are polynomials in the
commuting context involutions, `(FCF1)` implies

```text
p_(c,a)(A)S_c=S_cp_(c,a)(B).                           (FCF5)
```

The range projection `R_c=S_cS_c^*` is dominated by `E_c`, while
`p_(c,a)(A)E_c=0`.  Hence `p_(c,a)(A)S_c=0`, and `(FCF5)` gives

```text
Qp_(c,a)(B)=S_c^*p_(c,a)(A)S_c=0.                     (FCF6)
```

Taking trace and using `(FCF3)` yields

```text
0=Tr(Qp_(c,a)(B))
 =Tr(Q)tau(p_(c,a)(B)).                                (FCF7)
```

This contradicts full support `(FCC1)`.

The proof also explains the nonfactorial boundary.  Without factoriality,
`E_M(Q)` is a nonzero central positive density supported only on central
components where every excluded atom vanishes.  Thus exact common-source
covariance can only select pre-existing central cap components, in agreement
with `tracial-cap-menus-are-central-core-partitions`; an external isotypic or
multiplicity projection cannot refine support inside a full-support factor.
