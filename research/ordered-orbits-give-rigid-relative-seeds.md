---
rg: 2
id: ordered-orbits-give-rigid-relative-seeds
kind: claim
title: Corollary of bh-emitter-a's order seeds - the dilating stable letter that tree gluing cannot seed is a point stabilizer of the affine order, so the modular obstruction is sidestepped by order, not by the tree
distinct_from:
  order-seeds-are-rigid-relative-seeds: that is the theorem, with the same SFT, the same hypotheses and the proof (bh-emitter-a, refereed PASS); this only records how it meets the tree-gluing obstruction, and duplicates nothing.
  baumslag-gersten-groups-lie-in-class-c: that is where Baumslag–Gersten is placed in 𝒞 (refereed); this does not reprove it.
  dilating-edge-axes-admit-no-matched-gluing: that shows tree gluing over cyclic vertex seeds forces the modular character to be 1; this notes that the order seed of the theorem above realizes the excluded pair anyway.
---

**ESTABLISHED** as a direct corollary of `order-seeds-are-rigid-relative-seeds` (bh-emitter-a, 2026-09-18). The
theorem, its SFT, and Baumslag–Gersten `∈ 𝒞` (`baumslag-gersten-groups-lie-in-class-c`) are bh-emitter-a's. An
earlier version of this node (8a8a52553f) re-derived them independently. It was mathematically correct (referee
bh-ref-hl) but a duplicate, and it is reduced here to the one remark below. Lane bh-invent-03, 2026-09-19.

**Hypotheses.** My "positive connectivity" (chains of positive neighbours `g c s·p`, `c ∈ C`, `s·p > p`) is
equivalent to bh-emitter-a's monotone-path hypothesis (M), because steps inside `C` fix the position.

## Remark: two views of one dilation

- **The tree view.** In `BS(1,n) = ⟨a, b | b^(-1)ab = a^n⟩`, the subgroup `⟨b⟩` acts on the Bass–Serre tree along
  an axis of dilating edges. `dilating-edge-axes-admit-no-matched-gluing` shows no matched gluing of cyclic vertex
  seeds produces `(BS(1,n), ⟨b⟩)`: the tail period would have to be multiplied by `n` at every step.
- **The order view.** `⟨b⟩` is the stabilizer of `0` in the affine action on `Z[1/n]`. The order seed of
  `order-seeds-are-rigid-relative-seeds` realizes the pair with three letters, and the dilation costs nothing:
  `b` fixes `0`, and `a` moves every point up.
- **Lesson for general BH.** An obstruction to tree gluing is not an obstruction to seeding. Dilations that no
  tree can carry are carried by an invariant order on the vertex group. So the seed tower should look for ordered
  or affine structure in associated subgroups before gluing them.
