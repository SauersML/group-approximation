---
rg: 2
id: tree-product-lattice-nonsofic-gives-mixing-nonsofic-action
kind: claim
title: A nonsofic lattice with dense projections in a product of two tree groups gives every lattice there a free mixing nonsofic action
distinct_from:
  howe-moore-lattice-nonsofic-action-transfers-to-mixing: that needs a Howe-Moore envelope and moves nonsoficity within one lattice; this works in a product of two tree groups, which is not Howe-Moore, and moves nonsoficity from one lattice to every other lattice, such as a product of free groups
  product-tree-lattices-in-paunescu-class-iff-f2xf2: that transfers membership in Paunescu's class without any mixing; this produces mixing witnesses, at the price of a nonsofic seed lattice with dense projections
artifacts:
  - research/artifacts/product-tree-mixing-transfer-2026-09-12.md
---

**ESTABLISHED (unreviewed).** Let `L = G_1 × G_2` with `G_i` boundary-2-transitive simple
tree groups (`product-of-tree-groups-has-factorwise-howe-moore`), and let `Γ <= L` be a
lattice that is not sofic and whose projections to `G_1` and `G_2` are dense. Put
`B = ({0,1}, fair)^Γ` and `W = L ×_Γ B`, with `L` acting on the left. Then for every
lattice `Λ <= L`,

```text
Λ ↷ W = L ×_Γ ({0,1},fair)^Γ
```

is essentially free, mixing, and not sofic.

**Instance.** In `L^+ = Aut(T_p)^+ × Aut(T_q)^+` (`p, q >= 3`) take `Λ = K_p × K_q`, the
product of the torsion-free kernels of `C_2^(*p) → (C_2)^p` and `C_2^(*q) → (C_2)^q`, a
product of free groups that preserves vertex types. It is residually finite. So a
single nonsofic lattice of `L^+` with dense projections produces a free mixing nonsofic
action of a sofic group, answering `mixing-free-nonsofic-action-of-sofic-group`
(`mixing-nonsofic-action-from-tree-product-lattice`).

**Mechanism.** `L × B` couples `Λ` with `Γ`; the `Γ`-quotient carries the free action
`Γ ↷ (Λ\L) × B`, nonsofic because `Γ` is a nonsofic group, and
`sofic-free-actions-are-soe-invariant` moves this to `Λ ↷ W`. Dense projections and the
mixing Koopman representation of `B` make each factor `G_i` ergodic on `W`, and
factorwise Howe--Moore turns that into mixing. No Kazhdan subgroup is involved: lattices
in products of trees have the Haagerup property.

**Scope.** The seed must be a nonsofic group, not merely a group outside `𝒮`; the
ergodicity step uses the Bernoulli seed only. Proof in
`tree-product-lattice-mixing-transfer-proof`.
