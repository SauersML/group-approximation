---
rg: 2
id: orthogonal-steinberg-root-spectral-support-is-not-additive
kind: claim
title: Nontrivial spectral support of Steinberg roots is not additive on orthogonal idempotents
distinct_from:
  hs-full-rank-scalar-defect-blocks-naive-rank-decoding: That uses small full-rank perturbations to block HS-to-rank conversion; this is an exact zero-defect counterexample to additivity of root spectral support.
  local-steinberg-heisenberg-packets-are-coefficient-rank-blind: That varies the rank of one idempotent while fixing a local packet; this uses a full elementary-group representation and compares two orthogonal idempotents with their sum.
  hs-steinberg-morita-trace-additivity-on-adaptive-blocks: That allows a cross-block model-dependent physical mass; this rules out choosing that mass to be the support of each individual root word.
---

**ESTABLISHED FIREWALL.**  Let `k=F_p`, `R=k times k`, and take the
orthogonal idempotents

```text
q=(1,0),       d=(0,1),       q+d=1.
```

For `n>=3`,

```text
E_n(R)=E_n(k) times E_n(k).
```

Let `lambda` be the left regular representation of the finite group
`E_n(k)` and represent the product on
`l2(E_n(k)) tensor l2(E_n(k))`.  For one root position and
`u=lambda(x_ij(1))`, the three coefficient roots act as

```text
x_ij(q)   -> u tensor 1,
x_ij(d)   -> 1 tensor u,
x_ij(q+d) -> u tensor u.                               (RNSA1)
```

Every one of these is the regular action of a nonidentity order-`p` element
on its cyclic orbits.  Hence the projection onto the complement of its
`1`-eigenspace has normalized trace

```text
1-1/p.                                                  (RNSA2)
```

In particular

```text
supp(x_ij(q+d)-1)
 !=supp(x_ij(q)-1)+supp(x_ij(d)-1)                     (RNSA3)
```

at the level of normalized dimensions: the left side and each summand have
mass `1-1/p`.  For `p=2`, all three masses are `1/2`.

This exact representation satisfies the complete elementary-group and
Steinberg relations, not merely one Heisenberg window.  Therefore root
spectral support, root displacement, and any scalar depending only on the
individual cyclic root character cannot be the Morita trace in `(MTA2)`.
The missing invariant must inspect the simultaneous two-block placement.
