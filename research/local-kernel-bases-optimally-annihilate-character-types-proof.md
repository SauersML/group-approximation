---
rg: 2
id: local-kernel-bases-optimally-annihilate-character-types-proof
kind: route
title: Prove optimal annihilation by local kernel bases
target: local-kernel-bases-optimally-annihilate-character-types
requires: []
---

A character of `H` descends to `H/L` exactly when it is trivial on `L`.
The character-idempotent calculation `(FKQ5)` then gives `(LKB2)`.  If
`L=K`, the surviving marked packet is plainly `X_-(K)`.

Conversely suppose `L<K`.  Choose a character `eta_K` of `K` which is
trivial on `L` but nontrivial on `K`; such a character exists by duality for
the nontrivial quotient `K/L`.  Condition `(LKB1)` lets us prescribe

```text
eta|K=eta_K,                    eta(J)=1               (LKP1)
```

and extend these compatible values to a character of `H`.  The same
condition supplies a character `chi_0` of `H` satisfying

```text
chi_0|K=1,                     chi_0(J)=-1.            (LKP2)
```

Then `chi=chi_0 eta` belongs to `X_-(L)` but not to `X_-(K)`.  Hence equality
of the two marked packets forces `L=K`, proving `(LKB3)`.

The minimum cardinality of a subset generating `K` is by definition
`d(K)`, and for an elementary abelian group it is its vector-space
dimension.  For `(LKB5)`, every basis element lies in `ker(theta)`.  The
normal closure of all chosen local bases therefore remains in
`ker(theta)`, and `(FKQ5)` annihilates every character which is nontrivial
on the corresponding `K_c`.  This proves the contextual and presentation
claims.
