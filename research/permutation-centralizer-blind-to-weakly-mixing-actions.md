---
rg: 2
id: permutation-centralizer-blind-to-weakly-mixing-actions
kind: claim
title: The permutations of an embedded crossed product that commute with a weakly mixing subgroup are only the images of its centralizer, so Kun-Thom Theorem 4.1 sees only Theorem B
invalidates: [mixing-nonsofic-action-via-permutation-centralizers]
distinct_from:
  kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions: that covers the diagonal fixed algebra and Theorem C; this covers the permutation centralizer of Theorem 4.1, the one Kun-Thom input that node leaves open
  kun-thom-sofic-centralizer-normalization: that imports Theorem 4.1 about sofic representations; this computes what Theorem 4.1 can see of a weakly mixing free action inside a sofic embedding
artifacts:
  - research/artifacts/nonsofic-action-mixing-transfer-part2-2026-09-12.md
---

**ESTABLISHED.** Let `G ↷ (X,μ)` be an essentially free p.m.p. action of a countable group,
`M = L^∞(X) ⋊ G`, and `Θ : M → Π_(n→𝒰) M_(k_n)(C)` a sofic embedding (Păunescu Definition 1.4), with
`σ(g) = Θ(u_g)` and `𝒮_𝒰 = Π_(n→𝒰) P_(k_n)` the permutations of the ultraproduct. Let `Γ <= G` act
weakly mixingly on `(X,μ)`. Then

```text
Θ(M) ∩ C_(𝒮_𝒰)(σ(Γ)) = σ(C_G(Γ)).
```

Consequently, if `Γ <= G` is an infranormal Kazhdan pair with `G` Kazhdan, Kun--Thom Theorem 4.1
(`kun-thom-sofic-centralizer-normalization`), restricted to permutations lying in the embedded crossed
product, says only that `σ(C_G(Γ))` is normalized by `σ(G)`, i.e. that `C_G(Γ)` is normal in `G`. That
is Kun--Thom Theorem B, which holds for every sofic `G`. So it cannot contradict soficity of the action.
For a mixing free action every infinite `Γ` acts weakly mixingly, so this applies to all mixing
candidates in `mixing-free-nonsofic-action-of-sofic-group`.

**Scope.** Permutations of `C_(𝒮_𝒰)(σ(Γ))` outside `Θ(M)` are not covered. Those normalizing
`Θ(L^∞(X))` induce automorphisms of `(X,μ)` commuting with `Γ`, and a sofic embedding is under no
obligation to implement any given one. Theorem 4.1 constrains them, but the action does not force them
to exist.

Proof in `permutation-centralizer-blind-to-weakly-mixing-actions-proof`.
