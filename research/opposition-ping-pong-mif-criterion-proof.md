---
rg: 2
id: opposition-ping-pong-mif-criterion-proof
kind: route
title: Ping-pong along the poles of a proximal element gives a witness for every nontrivial mixed word
target: opposition-ping-pong-criterion-gives-mixed-identity-freeness
requires: []
---

Notation as in the target. For `γ ∈ G` write `ev_γ : G * ⟨x⟩ → G` for the
homomorphism with `ev_γ|_G = id` and `ev_γ(x) = γ`, so `w(γ) = ev_γ(w)`.

**Step 0: an infinite-order proximal element.** Apply (GP) to `F = ∅` to get a
proximal `h` with poles `(z₊, z₋)`. By (PR1) pick `y ∈ O(z₋)` with `y ≠ z₊`.
If `h^m = 1` for some `m ≥ 1`, then `h^{nm}(y) = y` for all `n`. But by (PR2)
with `K = {y}`, `h^{nm}(y)` eventually lies in any open `U ∋ z₊`, and by the
Hausdorff property some such `U` misses `y`. So `h` has infinite order.

**Step 1: reduction to cyclically reduced words.** Each `ev_γ` is a
homomorphism, so `w(γ) = 1` exactly when `(u w u⁻¹)(γ) = 1`, for any
`u ∈ G * ⟨x⟩`. Every nontrivial element of the free product `G * ⟨x⟩` is
conjugate to one of:

- (a) an element `g ∈ G ∖ {1}`;
- (b) a power `x^m` with `m ≠ 0`;
- (c) a word `g_1 x^{m_1} g_2 x^{m_2} ⋯ g_k x^{m_k}` with `k ≥ 1`, all
  `g_i ∈ G ∖ {1}` and all `m_i ≠ 0`.

Indeed, write the element in normal form as an alternating product of nontrivial
syllables from `G` and from `⟨x⟩`. If it has length at least two and its first
and last syllables lie in the same factor, conjugating by the first syllable
shortens it (the two syllables merge, or cancel and the neighbours merge).
Repeating ends at length one, which is (a) or (b), or at an alternating word of
even length. A cyclic permutation, which is a conjugation, makes such a word
start with a `G`-syllable, giving (c).

In case (a), `w(γ) = g ≠ 1` for every `γ`. In case (b), `w(h) = h^m ≠ 1` by
Step 0.

**Step 2: case (c).** Put `F = {g_1, …, g_k}` and take `h`, `(z₊, z₋)` as in
(GP). Write `s_i = sign(m_i) ∈ {+, −}`, `a_i = z_{s_i}` and
`B_i = O(z_{−s_i})`. We show `w(h^N) ≠ 1` for all large `N`. Note
`h^{N m_i} = (h^{s_i})^{N|m_i|}` and `N|m_i| ≥ N`, so (PR2) for `s_i = +` and
(PR3) for `s_i = −` give: for compact `K ⊆ B_i` and open `U ∋ a_i`,
`h^{N m_i}(K) ⊆ U` once `N` is large.

- **The start.** By (PR1), `B_k` has at least two points, so choose
  `z_0 ∈ B_k` with `z_0 ≠ g_1·a_1`. Choose disjoint open sets `V_0 ∋ z_0` and
  `V_1 ∋ g_1·a_1`, and put `K_k = {z_0}`, a compact subset of `B_k`.
- **The neighbourhoods.** Put `U_1 = g_1⁻¹(V_1)`, an open neighbourhood of
  `a_1`. For `i = 2, …, k` in turn:
  - by (GP) with `g = g_i`, `s = s_i` and `t = −s_{i−1}`, the point `g_i·a_i`
    lies in `B_{i−1}`, which is open by (PR1);
  - a compact Hausdorff space is regular, so there is a compact neighbourhood
    `K_{i−1}` of `g_i·a_i` inside `B_{i−1}`;
  - put `U_i = g_i⁻¹(int K_{i−1})`, an open neighbourhood of `a_i`.
- **The exponent.** Choose `N` so large that `h^{N m_i}(K_i) ⊆ U_i` for every
  `i = 1, …, k`. There are finitely many conditions, each holding for all
  large `N`.
- **The chase.** Reading `w(h^N)·z_0` from the right:
  - `h^{N m_k}(z_0) ∈ U_k`, since `K_k = {z_0}`;
  - for `i = k, …, 2`: a point of `U_i` is sent by `g_i` into
    `int K_{i−1} ⊆ K_{i−1}`, then by `h^{N m_{i−1}}` into `U_{i−1}`;
  - finally `g_1(U_1) = V_1`.

  So `w(h^N)·z_0 ∈ V_1`. Since `z_0 ∈ V_0` and `V_0 ∩ V_1 = ∅`, we get
  `w(h^N)·z_0 ≠ z_0`, hence `w(h^N) ≠ 1`.

For `k = 1` the list of neighbourhoods is just `U_1`, and (GP) is only used
through the existence of `h`.

In every case some `γ ∈ G` has `w(γ) ≠ 1`, so `G` is MIF. `∎`

**Where (GP) is used.** Only the pairs `(s, t) = (s_i, −s_{i−1})` occur. When
`m_{i−1}` and `m_i` have opposite signs this is `t = s`: the constant `g_i` must
move the pole `z_{s_i}` into `O(z_{s_i})`.
