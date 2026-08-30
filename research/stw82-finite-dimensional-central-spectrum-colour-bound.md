---
rg: 2
id: stw82-finite-dimensional-central-spectrum-colour-bound
kind: claim
title: Finite-dimensional central support spectra cost at most dimension times multiplicity
artifacts:
  - research/artifacts/stw82-finite-dimensional-support-spectrum-audit-2026-08-30.md
distinct_from:
  stw82-zero-dimensional-central-supports-recolour-pointwise: that obtains the pointwise-optimal multiplicity when the common spectrum has dimension zero; this pays one copy of that multiplicity for each of `n+1` discrete refinement families.
  stw82-spectral-interval-band-depth-reuses-colours: that assumes prescribed interval localization for supports coming from one functional-calculus variable; this permits arbitrary support functions over any compact metrizable finite-dimensional common spectrum.
  stw82-support-local-coupled-covers-merge-colours: that repairs maps after suitable cutters have been supplied; this constructs the cutters from finite covering dimension and preserves order zero without repair.
---

Let `V` be finite, let `F_v` be unital C*-algebras, and let

```text
phi_v:F_v->B
```

be cpc order-zero maps.  Put `h_v=phi_v(1_(F_v))` and discard the zero
maps.  Suppose there is a unital abelian C*-algebra

```text
C subseteq M(B) intersect (union_v phi_v(F_v))'
```

which contains every `h_v`.  Suppose its spectrum `X` is compact metrizable
with covering dimension at most `n`, and put

```text
m=max_(x in X) |{v:h_v(x)>0}|.                       (D1)
```

Then, for every `epsilon>0`, there are positive contractions

```text
c_(v,i,k) in C,       i=0,...,n,  k=1,...,m,
```

such that

```text
c_(v,i,k)c_(w,i,k)=0                     (v!=w),     (D2)
norm((1-sum_(i,k)c_(v,i,k))h_v)<epsilon.             (D3)
```

The cut maps

```text
psi_(v,i,k)(a)=c_(v,i,k)phi_v(a)                    (D4)
```

are cpc order zero, satisfy

```text
norm(phi_v-sum_(i,k)psi_(v,i,k))<epsilon,            (D5)
```

and, for every fixed pair `(i,k)`, their direct sum over `v` is cpc order
zero.  Thus the outgoing family can be replaced, to arbitrary accuracy, by
at most

```text
(n+1)m                                                (D6)
```

global order-zero colours.

Consequently, if a C*-algebra `A` has arbitrarily accurate
finite-dimensional nuclear approximations whose outgoing supports admit
such a common algebra with `dim(X)<=n` and pointwise multiplicity at most
`m`, then

```text
dim_nuc(A)<=(n+1)m-1.                                (D7)
```

No claim of optimality is made when `n>0`.  The theorem is a constructive
upper bound; the zero-dimensional result shows that it specializes to the
sharp value `m` when `n=0`.

