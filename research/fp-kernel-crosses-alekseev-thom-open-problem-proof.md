---
rg: 2
id: fp-kernel-crosses-alekseev-thom-open-problem-proof
kind: route
title: Restrict soficity to the kernel and exclude residual finiteness through the mapping torus
target: fp-kernel-crosses-alekseev-thom-open-problem
requires:
  - mapping-torus-mf-radical-lies-in-finite-residual
artifacts:
  - research/artifacts/alekseev-thom-fp-kernel-boundary-2026-08-26.md
---

Let `G,K` satisfy the split-cyclic target and additionally assume that `K` is
finitely presented.  Subgroup permanence of soficity gives `K` sofic, and the
target already supplies property `(T)`.

Choose `t in G` mapping to `1 in G/K~=Z`.  Since `t` has infinite order modulo
`K`, the extension splits and conjugation by `t` defines an automorphism `phi`
with

```text
G ~= K semidirectProduct_phi Z.                         (ATK2)
```

Property `(T)` makes `K` finitely generated.  Apply
`mapping-torus-mf-radical-lies-in-finite-residual` to `(ATK2)`.  It gives

```text
Rad_MF(G) <= R_fin(K) x {0}.
```

The target identifies the left side with `K x {0}`, so `R_fin(K)=K`.
Equivalently, every homomorphism from `K` to a finite group is trivial.  Since
`K` is nontrivial, it is in particular not residually finite.

Therefore `K` has all four properties in `(ATK1)`, exactly giving a positive
answer to Alekseev--Thom Open Problem 6.1.
