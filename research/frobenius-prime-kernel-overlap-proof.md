---
rg: 2
id: frobenius-prime-kernel-overlap-proof
kind: route
title: Use uniqueness of the K times N support decomposition
target: frobenius-q-supported-overlap-contains-prime-kernel
requires: []
---

Since `aq=a`, one has `ae_N=0`.  Suppose for contradiction that
`K intersection N` is trivial.  Write

```text
a=sum_(k in K) alpha_k k
```

with finite support.  The multiplication map

```text
K times N -> Gamma,
(k,n) |-> kn
```

is injective: if `kn=k'n'`, then

```text
k^(-1)k'=nn'^(-1) in K intersection N={1}.
```

Therefore the group-basis expansion

```text
ae_N=(1/p)sum_(k,n)alpha_k kn                         (QPP1)
```

has coefficient `alpha_k/p` at every distinct word `kn`.  It can vanish only
when every `alpha_k` vanishes, contrary to `a!=0`.  Hence
`K intersection N` is nontrivial.  Since `N` has prime order, it follows
that `N<=K`, proving `(QPK1)`.

For the carrier application, `p_x<=q_c` gives `p_xq_c=p_x`, while
`common-carrier-lives-in-packet-intersection` places `p_x` in the group
algebra of the intersection of all incident packet groups.  Apply `(QPK1)`
inside each incident packet.  Two order-`p` kernels contained in the same
intersection must coincide.
