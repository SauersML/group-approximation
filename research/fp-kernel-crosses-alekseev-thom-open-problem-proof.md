---
rg: 2
id: fp-kernel-crosses-alekseev-thom-open-problem-proof
kind: route
title: Restrict soficity to the kernel and exclude residual finiteness through the mapping torus
target: fp-kernel-crosses-alekseev-thom-open-problem
requires:
  - finitely-generated-rf-automorphism-mapping-torus-is-rf
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

Property `(T)` makes `K` finitely generated.  If `K` were residually finite,
`finitely-generated-rf-automorphism-mapping-torus-is-rf` applied to `(ATK2)`
would make `G` residually finite, hence operator-MF.  But the target says
`Rad_MF(G)=K` and `K!=1`, whereas an operator-MF group has trivial MF radical.
This contradiction proves that `K` is not residually finite.

Therefore `K` has all four properties in `(ATK1)`, exactly giving a positive
answer to Alekseev--Thom Open Problem 6.1.
