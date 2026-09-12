---
rg: 2
id: spherical-artin-linearity-over-q-x-y-proof
kind: route
title: Crisp's product embedding plus block sums of the faithful LKB representations over Q(x,y)
target: spherical-artin-groups-are-linear-over-q-x-y
requires: []
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

Literature derivation. Read on 2026-09-12 from L. Paris, *Braid groups and Artin
groups*, arXiv:0711.2372, §6 and §6.1, extracted on MSI.

1. **Crisp** [57], quoted by Paris: every spherical-type Artin group embeds in a
   direct product `P = A(Γ_1) × ... × A(Γ_r)` whose factors have types A_n, D_n
   or E_k.
2. **Faithful factors.** Each `Γ_i` is of small type without triangle and of
   spherical type. Corollary 6.5 (Bigelow, Krammer, Digne, Cohen--Wales) gives a
   faithful `ˆΦ_i : A(Γ_i) -> GL(V_i)`, where `V_i` is a finite-dimensional
   vector space over `K = Q(x,y)`, the same field for every `i`.
3. **Block sum.** `⊕ ˆΦ_i : P -> GL(V_1 ⊕ ... ⊕ V_r)` is injective, because an
   element of `P` in its kernel has every coordinate in some `ker ˆΦ_i = 1`.
4. **Conclusion.** Restricting to `A(Γ) <= P` gives a faithful representation
   in `GL_N(Q(x,y))`, with `N = Σ dim V_i`. QED

Not reproved beyond the assembly.
