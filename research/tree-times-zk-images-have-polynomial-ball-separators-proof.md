---
rg: 2
id: tree-times-zk-images-have-polynomial-ball-separators-proof
kind: route
title: Cut at the weighted tree centroid of the image; the L-slab over it is O(D^k) points, and no short edge crosses it
target: tree-times-zk-images-have-polynomial-ball-separators
requires: []
---

Write `p = π_T ∘ f` and `q = π_(Z^k) ∘ f`.

**Item 1.**
- Fix finite `A ⊆ B_X(x, D)`. Put the measure `μ(v) = |A ∩ p⁻¹(v)|` on `V(T)`.
- *Centroid.* Some vertex `c` has `μ(C) ≤ |A|/2` for every component `C` of `T ∖ {c}`. This is standard:
  start anywhere, and step into the unique component of mass `> |A|/2` while one exists. Each step
  strictly shrinks the heavy side, so the walk stops at such a `c`.
- *Separator.* Let `S = {a ∈ A : d_T(p(a), c) ≤ L}`.
- *No edge crosses.* Let `a, b ∈ A ∖ S` be adjacent in `X`. Then `d_T(p(a), p(b)) ≤ L`. If the tree
  geodesic `[p(a), p(b)]` contained `c`, then `d_T(p(a), c) + d_T(c, p(b)) ≤ L`, so `a ∈ S`, which is a
  contradiction. So `p(a)` and `p(b)` lie in one component of `T ∖ {c}`.
- *Balanced.* By induction along paths, `p` maps each connected component of `X[A ∖ S]` into a single
  component `C` of `T ∖ {c}`. That component of `X[A ∖ S]` has at most `μ(C) ≤ |A|/2` vertices.
- *Size.* Every `a ∈ S` has `p(a) ∈ B_T(c, L)`. Also `|q(a) − q(x)|₁ ≤ LD`, because `f` is `L`-Lipschitz
  and `d(a, x) ≤ D`. So `f(S)` lies in `B_T(c, L) × B_(Z^k)(q(x), LD)`, a set of at most
  `|B_T(L)|·(2LD+1)^k` points. With fibres of size at most `m`, this gives
  `|S| ≤ m·|B_T(L)|·(2LD+1)^k`.
- Here `|B_T(L)|` is the largest `L`-ball of `T`, which is finite because `T` has bounded degree. ∎

**Item 2.**
- `f(z·s) = φ(z·s)^(−1) = (bφ(z))^(−1) = φ(z)^(−1)·b^(−1)` for some `b ∈ B`, and right multiplication by
  `b^(−1)` moves a point of the Cayley graph by `|b|`.
- So Schreier edges map to paths of length at most `L`, and `f` is injective because inversion is. Apply
  item 1 with `m = 1`. ∎

**Item 3.**
- Let `S_Q` generate `Q` and let `ℓ = max_(t ∈ S_Q) |t|_S`. The map `o : Cay(Q, S_Q) → Sch(G, Z, S)` given
  by `o(t) = x·t` is `ℓ`-Lipschitz. Its fibres are left cosets of `Q ∩ G_x`, of size `m = |Q ∩ G_x|`.
- So `f ∘ o` is `ℓL`-Lipschitz into `T_(2d)×Z^2` with fibres of size at most `m`. Item 1 gives
  `bsep_Q(D) ≤ m·|B_T(ℓL)|·(2ℓLD+1)^2 = O(D^2)`.
- *`Z^4`.* The `D`-ball contains a box of side `⌊D/4⌋`. A balanced separator of the `n`-box in `Z^4` has
  size `≳ n^3`, by recalled box isoperimetry. So `bsep ≳ D^3`.
- *`F₂×F₂`.* The `D`-ball contains `B_T(⌊D/2⌋)²`, which has `N ≍ 3^D` vertices. Its balanced separators
  have size `≳ N/log N`, by recalled Benjamini–Schramm–Timár. So `bsep` grows exponentially in `D`.
- Either growth contradicts `O(D^2)`. The general case is the hypothesis itself. ∎

**Remark (why no global profile is used).** The global profile `sep(T×Z^2)` does not suffice. A subset
lying in a single slab `{v}×Z^2` has separators of size `≍ n^(1/2)`, and a ball of radius `D` in a
Kazhdan Schreier graph has `n ≥ e^(cD)` points. Localizing to balls is what turns the bound into `O(D^2)`,
that is, `O((log n)^2)`.
