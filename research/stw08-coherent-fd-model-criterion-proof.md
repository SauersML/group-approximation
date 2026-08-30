---
rg: 2
id: stw08-coherent-fd-model-criterion-proof
kind: route
title: Take pointwise limits in one finite-dimensional inductive system
target: stw08-af-embedding-iff-summably-coherent-fd-models
requires: []
---

Suppose first that the displayed system exists, and let

```text
E=lim (F_n,alpha_n).
```

For fixed `a_j`, the images of `phi_n(a_j)` in `E` form a Cauchy sequence,
because the consecutive errors are eventually bounded by the summable series
`sum 2^(-n)`.  Contractivity and density extend its limit to a u.c.p. map
`Phi:A->E`.  The multiplicativity tests, together with density and the
coherence estimates, show that `Phi(ab)=Phi(a)Phi(b)` for all `a,b in A`.
The norm tests give `||Phi(a)||=||a||` first on the dense test set and then on
all of `A`.  Thus `Phi` is an embedding into the AF algebra `E`.

Conversely, let `eta:A->E` be an embedding into a unital AF algebra, replacing
`E` by the corner `eta(1)E eta(1)` if necessary.  Write `E` as the closure of
an increasing sequence of unital finite-dimensional subalgebras `F_n`.
Finite-dimensional C\*-algebras are injective operator systems, so for each
`n` there is a u.c.p. retraction `P_n:E->F_n` fixing `F_n`.  If `x in F_n`,

```text
||P_n(eta(a))-eta(a)|| <= 2||eta(a)-x||.
```

Pass to a subsequence of the `F_n` so that the first `n` test elements are
within a sufficiently small, summable tolerance of `F_n`, and put
`phi_n=P_n eta`.  These maps are summably coherent after the inclusions
`F_n->F_{n+1}` because both successive values are close to `eta(a_j)`.
The same estimate gives asymptotic multiplicativity and isometry.  This is the
required system.

For nonunital `A`, its minimal unitization is exact or quasidiagonal whenever
`A` is, and the unitization of an AF algebra is AF.  Hence the unital criterion
applies without changing AF-embeddability.
