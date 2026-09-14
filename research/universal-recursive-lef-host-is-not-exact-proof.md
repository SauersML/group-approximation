---
rg: 2
id: universal-recursive-lef-host-is-not-exact-proof
kind: route
title: A recursively presented residually finite non-exact group lies in the universal recursive LEF host
target: universal-recursive-lef-host-is-not-exact
requires: [recursive-residually-finite-non-exact-groups-exist, simple-kazhdan-lef-host-for-recursive-lef-groups]
artifacts:
  - research/artifacts/sk-free-1-exactness-2026-09-13-part2.md
---

1. **Input.** `recursive-residually-finite-non-exact-groups-exist` gives Γ, recursively presented, f.g. and residually finite, without property A.
2. **Γ lies in the host.** Γ is LEF: finite quotients injective on balls are partial models. So Γ lies in the host H of `simple-kazhdan-lef-host-for-recursive-lef-groups`.
3. **No property A.** With finite generating sets, the identity (Γ,d_Γ) → (Γ, d_H restricted) is uniformly expansive and effectively proper. So Γ is coarsely equivalent to a subspace of H.
4. **Transfer.** Property A is a coarse invariant and passes to subspaces (Willett, arXiv:math/0612492 l.542, l.1228–1229), so H has no property A.
5. **Exactness.** For countable groups, no property A means C*_r(H) is not exact (Guentner–Kaminker, Ozawa; quoted from arXiv:1406.5015 l.166).
6. **Hyperlinearity.** H is LEF, so L(H) ⊆ R^ω.
