---
rg: 2
id: finite-group-shared-overlap-polar-alignment
kind: claim
title: Two flexible exactifications of one approximate finite-group action align on a large exact common submodule
distinct_from:
  finite-schur-clifford-packet-flexible-hs-exactification: that exactifies one local packet; this compares two resulting exact representations through their shared approximate subgroup action.
  scaled-kazhdan-transport: that transports asymptotic commutants under a Kazhdan action; this is a finite-group averaging and polar-decomposition lemma with an explicit dimension-loss bound.
---

Let `A` be a finite group, let `f:A->U(d)` be any map, and for `i=1,2` let

```text
rho_i:A->U(m_i),                 V_i:C^d->C^(m_i)
```

be an exact representation and an isometry. Define

```text
eta_i^2=(1/(|A|d)) sum_(a in A)
          ||rho_i(a)V_i-V_i f(a)||_F^2,
eta=eta_1+eta_2.
```

Then there are `A`-invariant subspaces `K_i subset C^(m_i)` and a unitary
intertwiner

```text
W:K_1->K_2,                    W rho_1(a)=rho_2(a)W on K_1,
```

such that

```text
dim K_1=dim K_2 >= (1-4 eta^2)d.                                (OPA1)
```

Thus context-dependent Gowers--Hatami corrections do not by themselves
destroy a shared finite packet: whenever both corrected packets approximate
the same original selector words, all but `O(eta^2 d)` dimensions can be
identified by an exact common-subgroup intertwiner.
