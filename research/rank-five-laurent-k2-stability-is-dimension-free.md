---
rg: 2
id: rank-five-laurent-k2-stability-is-dimension-free
kind: claim
title: Rank-five Laurent K2 stability is independent of spectator polynomial dimension
distinct_from:
  stable-laurent-k2-has-minimal-three-symbol-packet: that proves the three-symbol quotient in the classical range r>=d+3; this improves the threshold to r>=5 by removing polynomial variables before applying stability
  two-coordinate-relators-leave-stable-laurent-k2: that detects the stable Laurent kernel; this identifies the same kernel with fixed-rank K2 for every r>=5
  opposite-transvections-are-first-nonore-relative-gate: that includes the pinned rank-three gate; this leaves ranks three and four outside the theorem and makes no RE/C conclusion
---

Let `k=F_q`, let `d>=2`, and put

```text
A=k[x_1^(+-1),x_2^(+-1)],
R_d=A[x_3,...,x_d].
```

For every matrix rank `r>=5`, stabilization is an isomorphism

```text
K2(r,R_d) -> K2(R_d).                                       (RFL1)
```

Hence

```text
K2(r,R_d) ~= Z (+) C_(q-1) (+) C_(q-1),                    (RFL2)
```

with generators

```text
c(x_1,x_2),       c(a,x_1),       c(a,x_2),                 (RFL3)
```

where `a` generates `k^*`.  In particular, for every `r>=5`, with no
condition `r>=d+3`,

```text
St_r(R_d)/<<the three symbols in (RFL3)>> ~= E_r(R_d).       (RFL4)
```

For `q>2` the packet remains normal-minimal.  For `q=2`, only the first
symbol is needed.

The rank bound is honest.  The unstable A1-invariance input starts at root
system `A_4`, hence matrix rank five.  This argument says nothing about
`K2(3,R_d)` or `K2(4,R_d)`, and in particular does not close the pinned
rank-three opposite-compressor problem.

DERIVATION
a1-invariance-removes-polynomial-dimension-proof
