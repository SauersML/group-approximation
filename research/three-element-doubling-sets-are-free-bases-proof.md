---
rg: 2
id: three-element-doubling-sets-are-free-bases-proof
kind: route
title: Ping-pong on the free group gives a 2-fold matching; conversely a 2-fold matching for {1, a, b} splits the subgroup into four ping-pong pieces for a and b a^-1
target: three-element-doubling-sets-are-free-bases
requires: []
---

Complete argument: `research/artifacts/three-element-doubling-sets-2026-09-16.md`, §1 (item 1), §2
(item 2), §4 (item 3). Outline:

**Item 1, free ⇒ doubles.** In `H = <a, b>` free on `a, b`, let `W(t)` be the reduced words beginning
with `t`. Then `H = W(a) ⊔ a W(a^-1) = W(b) ⊔ b W(b^-1)`, which defines an injection
`μ : H × {1, 2} -> H` with `μ(y, i) ∈ {1, a, b} y`. Hence `|{1, a, b} Y| >= 2|Y|` on `H`, and on `G` by
splitting `Y` along right cosets of `H`.

**Item 1, doubles ⇒ free.**
- Hall's condition holds for the graph `H × {1, 2} -> H`, `(y, i) -> {y, a y, b y}`. The finite Hall
  theorem and König's lemma give an injective `μ` with `μ(y, i) ∈ {y, a y, b y}`.
- Let `B` be the set of `y` with `μ(y, i) = y` for some `i`, `A = H \ B`. Injectivity gives
  `a A, b A ⊆ A`, `a A ∩ b A = ∅`, and an injection `φ : B -> A \ (a A ∪ b A)` with
  `φ(y) ∈ {a y, b y}`. Split `B = B_a ⊔ B_b` by which value `φ` takes.
- The pieces `P_1 = a A`, `P_2 = B`, `Q_1 = b A ∪ b B_b`, `Q_2 = a B_a` are pairwise disjoint and
  nonempty, and `H = P_1 ⊔ a P_2 = Q_1 ⊔ h Q_2` with `h = b a^-1`.
- Ping-pong with `X(a) = P_1`, `X(a^-1) = P_2`, `X(h) = Q_1`, `X(h^-1) = Q_2` shows that `a, h` are a
  free basis. The Nielsen move `(a, h) -> (a, h a) = (a, b)` gives item 1.

**Item 2.** Write `S = s_0 {1, a, b}` and use invariance and item 1; for `|S| = 2` take
`Y = {1, c}` where `S = s_0 {1, c}`; for `|S| = 1` take `Y = {1}`.

**Item 3.**
- Suppose `T(G) = 5`. Every paradoxical decomposition has `m, n >= 2`, and a free subgroup would give a
  four-piece one (the sets `W(t)` lifted along cosets). So `G` has no non-abelian free subgroup.
- A five-piece decomposition `G = P_1 ∪ P_2 g_2 = Q_1 ∪ Q_2 h_2 ∪ Q_3 h_3`, normalized so that
  `g_1 = h_1 = 1`, gives an injection `(y, i) -> μ_i(y) ∈ y {1, g_2^-1, h_2^-1, h_3^-1}`.
- Inverting, `{1, g_2, h_2, h_3}` doubles. It has at least four elements by item 2.
- Existence of such `G` is imported from Ershov–Golan–Sapir (Adv. Math. 284 (2015), arXiv:1401.2202,
  abstract) and Golan (arXiv:1406.2097, abstract), both read on 2026-09-16.

Nothing about Thompson's group is used; the target's paragraph on `F` only points to
`thompson-f-support-three-pairs-have-common-multiples`, which has its own route.
