---
rg: 2
id: invariant-free-near-state-regular-cover-proof
kind: route
title: Pass the near map through its tracial null ideal
target: invariant-free-near-state-is-amenable-regular-cover
requires: []
---

Write `u_g=pi(g)`. Invariance immediately gives centrality of every near
generator with respect to `phi`: for arbitrary `T in B(H)`, apply invariance
to `T u_g` to obtain

```text
phi(u_g T)=phi(T u_g).                                  (ANP1)
```

The centralizer of a state is a C-star subalgebra, so `A=C^*(u_g:g in G)` is
contained in the centralizer of `phi`. Therefore `tau=phi|_A` is tracial and
`phi` itself is an `A`-central extension of `tau` to `B(H)`. This is exactly
amenability of the trace `tau`.

For a trace, the GNS null space

```text
I_tau={a:tau(a^*a)=0}
```

is a closed two-sided ideal. Indeed left multiplication is bounded in the
GNS seminorm, while for right multiplication traciality gives

```text
tau((ab)^*(ab))=tau(a^*a b b^*)<=||b||^2 tau(a^*a).
```

Every multiplicative defect belongs to `I_tau` by the near-representation
hypothesis. Hence the classes `v_g=u_g+I_tau` satisfy

```text
v_g v_h=v_(gh),   v_g^*=v_(g^-1),   v_e=1,             (ANP2)
```

so they are a genuine unitary representation of `G` generating `A/I_tau`.
The quotient trace is faithful by construction and has

```text
bar tau(v_g)=delta_(g,e).                               (ANP3)
```

In its GNS space the vectors `v_g Omega` are therefore an orthonormal basis:
their linear span is dense because the `v_g` generate the quotient, and
`<v_g Omega,v_h Omega>=bar tau(v_(g^-1 h))=delta_(g,h)`.
Left multiplication by `v_g` is consequently the left regular
representation on `ell^2(G)`. Since `bar tau` is faithful, this GNS
representation is faithful on `A/I_tau`; its C-star norm is therefore the
reduced group norm. This proves the trace-preserving isomorphism

```text
A/I_tau ~= C^*_r(G).
```

Finally, a singular positive functional on `B(H)` vanishes on `K(H)` (and
conversely), so a purely singular `phi` factors through `B(H)/K(H)`. This
proves the final Calkin-supported clause without changing the quotient
argument.
