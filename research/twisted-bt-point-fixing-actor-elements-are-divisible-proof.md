---
rg: 2
id: twisted-bt-point-fixing-actor-elements-are-divisible-proof
kind: route
title: A mixed-radix register on a coordinate the element ignores, with overflow applying the element, gives roots of every order
target: twisted-bt-point-fixing-actor-elements-are-divisible
requires:
  - twisted-brin-thompson-finite-presentation-criterion
---

**Registers.** Use the digit codes of `rationals-embed-in-brin-thompson-group-2v-proof`:
`c_(r,i) = 1^i 0` for `0 <= i <= r-2` and `c_(r,r-1) = 1^(r-1)`. Each `y ∈ C_*`
factors as `y = c_(2,d_1) ⋯ c_(n+1,d_n) w` with `d_i ∈ {0, …, i}`, and
`N_n(y) = Σ_i d_i (n+1)!/(i+1)!` runs over `{0, …, (n+1)! − 1}`.

**Item 1.** Put `r_0 = h`. For `n >= 1` and `(y, z) ∈ C_* × C^(S\{*})`, let
`r_n(y, z) = (y', h'^q(z))`. Here `N_n(y) + 1 = q (n+1)! + N'` with
`q ∈ {0, 1}`, and `y'` is `y` with its first `n` digit codes replaced by the
codes of `N'`.
- **`r_n ∈ SV_G`.**
  - It is a bijection, with inverse given by subtracting 1.
  - On each cylinder `{y ∈ c_(2,d_1)⋯c_(n+1,d_n)C}` with `N_n < (n+1)! − 1`, it
    agrees with `(v, 1) ∈ V wr G`, where `v ∈ ⊕_S V` is supported at `*` and is
    any element of `V` mapping the cone of the old codes onto the cone of the
    new codes by prefix replacement.
  - On the top cylinder `N_n = (n+1)! − 1`, near each point it agrees with
    `(v_0, 1)·(u, k)`. Here `(u, k) ∈ V wr G` agrees with `h` near that point,
    and `v_0` is supported at `*` and resets the codes by prefix replacement.
  - This uses that `h` does not change or read the coordinate `*`, so after `h`
    the point is still in the top cylinder.
  - So `r_n` is a homeomorphism that locally agrees with elements of `V wr G`.
- **Relations.** The proof in `rationals-embed-in-brin-thompson-group-2v-proof`
  uses only two facts about `s_0 = t × id`: it commutes with every rewrite of
  the register coordinate, and it has infinite order. Both hold for `h`, because
  `h = id_(C_*) × h'`. So the same computation gives
  `r_n^k(y, z) = (codes of (N_n(y)+k) mod (n+1)!, h'^(⌊(N_n(y)+k)/(n+1)!⌋)(z))`.
  It also gives `r_n^(n+1) = r_(n−1)`, and
  `∪_n <r_n> ≅ ∪_n (1/(n+1)!) Z = Q` with `h = r_0 ↦ 1`.
- **Actor elements.** If `g ∈ G` fixes `*`, then as a coordinate permutation
  `g = id_(C_*) × g'`. It has infinite order in `SV_G` exactly when it does in
  `G`, because the action on `C^S` is faithful when `G ↷ S` is faithful.

**Item 2.** Build a register `r^(i)_n` for `g_i` on coordinate `*_i`.
- For `i != j`, the elements `r^(i)_n` and `r^(j)_m` commute. Each changes only
  its own register coordinate. Its overflow condition reads only its own
  register. The overflow maps `g_i` and `g_j` commute and fix every `*_l`.
- So the group generated is abelian, and it is the union over `n` of
  `(1/(n+1)!) <g_1, …, g_k>`.
- This is `Q ⊗ Z^k = Q^k` when `<g_1, …, g_k> ≅ Z^k`.

**Item 3.** Type (A) passes to `S^+`.
- The action is faithful, because it already is on `S`. `G` is finitely
  presented.
- `Stab_G(*_i) = G` is finitely generated, and the stabilizers of points of `S`
  are unchanged.
- Two-element subsets:
  - those inside `S` have finitely many orbits by hypothesis;
  - the subsets `{*_i, *_j}` are fixed;
  - the orbits of `{s, *_i}` correspond to the `G`-orbits on `S`.
- There are only finitely many `G`-orbits on `S`. Suppose `s_1, s_2, …` lie in
  pairwise different orbits. Then the pairs `{s_1, s_i}`, `i >= 2`, lie in
  pairwise different orbits of pairs: `g{s_1, s_i} = {s_1, s_j}` with `i != j`
  would force `g s_i = s_1`, in a different orbit.
- `twisted-brin-thompson-finite-presentation-criterion` then says that
  `S^+V_G` is finitely presented, simple, and contains `G`. Items 1–2 apply
  inside it. ∎
