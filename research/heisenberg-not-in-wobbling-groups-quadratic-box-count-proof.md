---
rg: 2
id: heisenberg-not-in-wobbling-groups-quadratic-box-count-proof
kind: route
title: The Heisenberg centre fills a sqrt(N) ball; a quadratic ball bound forces short stabilizer elements whose commutator is a bounded power of c
target: heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs
requires: []
artifacts:
  - experiments/heisenberg-quadratic-growth-hosts-2026-09-17/check.py
  - experiments/heisenberg-quadratic-growth-hosts-2026-09-17/output.txt
---

**Conventions.**
- `[x, y] = x y x^(-1) y^(-1)`, and `c = [a, b]` is central in `H`.
- For a bijection `g` of `V`, `disp(g) = sup_v d(v, g v)`. Then `disp(g^(-1)) = disp(g)` and
  `disp(gh) ≤ disp(g) + disp(h)`.
- So if every generator in a finite symmetric `S` has displacement `≤ K`, a word of length `ℓ`
  moves every vertex by at most `Kℓ`. In item 1, `S = {a^(±1), b^(±1)}` and `K` is an integer,
  a supremum of integer distances. If `K = 0`, then `ρ` is trivial and there is nothing to prove.

**Step 0 (distortion of c).**
- Commutators with a central element are bilinear, so `[a^σ, b^τ] = c^(στ)` for all
  `σ, τ ∈ Z`.
- For `N ≥ 1` let `n = ⌊√N⌋`. Then `c^N = [a^n, b^n] c^(N − n^2)` with
  `0 ≤ N − n^2 ≤ 2n`, and `c` is a word of length 4.
- So `|c^(±N)| ≤ 4n + 4·2n = 12n ≤ 12√N`.
- Numerically checked for `N ≤ 16` (`check.py`: `|c^N| = 4√N` at squares).

**Step 1 (the a-box).**
- Fix `v ∈ V`. Let `L ∈ {1, 2, ..., ∞}` be the size of the `⟨c⟩`-orbit of `v`, and assume
  `L ≥ s_0^2`.
- Choose an integer `R ≥ s_0` with `R^2 ≤ L`: take `R = s_0` if `L = ∞`, and `R = ⌊√L⌋`
  otherwise.
- Consider the `(s_0 + 1)R^2` pairs `(s, u)` with `0 ≤ s ≤ s_0` and `0 ≤ u < R^2`, and the points
  `p(s, u) = a^s c^u v`.
- *Radius.* `a^s c^u` has word length `≤ s + 12√u ≤ s_0 + 12R ≤ 13R`, so
  `p(s, u) ∈ B(v, 13KR)`.
- *Collisions.* Suppose `p(s, u) = p(s', u')` with `s ≥ s'`. Since `a` and `c` commute,
  `a^(s−s') c^(u−u')` fixes `v`.
- *Contrapositive.* Suppose no element `a^σ c^μ` with `1 ≤ σ ≤ s_0` and `μ ∈ Z` fixes `v`. Then
  every collision has `s = s'`. Moreover `c^(u−u')` fixes `v` with `|u − u'| < R^2 ≤ L`, so
  `u = u'`.
- The `(s_0+1)R^2` points are then distinct and lie in `B(v, 13KR)`. So
  `(s_0 + 1)R^2 ≤ C(13KR)^2 = 169CK^2 R^2 ≤ s_0 R^2`, which is false.
- Hence there are `1 ≤ σ ≤ s_0` and `μ ∈ Z` with `a^σ c^μ v = v`.

**Step 2 (the b-box).** The same count with `b` in place of `a` gives `1 ≤ τ ≤ s_0` and `ν ∈ Z` with
`b^τ c^ν v = v`. Step 0 applies verbatim, because `b` also commutes with `c`.

**Step 3 (commutator).**
- The stabilizer of `v` is a subgroup, so it contains
  `[a^σ c^μ, b^τ c^ν] = [a^σ, b^τ] = c^(στ)`, using centrality of `c`.
- So `L` divides `στ ≤ s_0^2`, and hence `L ≤ s_0^2`.
- Together with Step 1, which assumed `L ≥ s_0^2`: every `⟨c⟩`-orbit has size `≤ s_0^2`.
- So `c^M` fixes every vertex for `M = lcm(1, ..., s_0^2)`. Since `c^M ≠ 1` in `H`, `ρ` is not
  injective.
- `SL_n(Z)` with `n ≥ 3` contains `H` as its upper unitriangular `3×3` block, so it is also
  excluded. This proves item 1.

**Step 4 (item 2).**
- Make `X` a graph `Γ_X` by joining `x` to `t x` for each `t ∈ T`.
- `B(x, r) ⊆ B_P(r) x`, so `|B(x, r)| ≤ |B_P(r)| ≤ C r^2`.
- If `g ∈ [[P ↷ X]]` with finite `F`, then `d(x, g x) ≤ max_(p ∈ F) |p|_T`, so
  `[[P ↷ X]] ≤ W(Γ_X)`, and item 1 applies.
- For `P = Z^2` with `T = {±e_1, ±e_2}`: `|B_P(r)| = 2r^2 + 2r + 1 ≤ 5r^2`.
- A topological full group consists of bijections that are piecewise given by finitely many
  elements of `P` on a finite clopen partition, so it lies in `[[P ↷ X]]`.

**Step 5 (item 3).**
- Let `K = max_(s ∈ S) disp(s)`, and `m_N = max_(0 ≤ k < N) |g^k|_S`. Then `m_N = o(N^(1/d))`,
  because `|g^k| = o(k^(1/d))` and each `|g^k|` is finite.
- Choose `N_0` such that `C (K m_N + 1)^d < N` for all `N ≥ N_0`.
- Fix `v`, and let `L` be the size of its `⟨g⟩`-orbit. Suppose `L ≥ N_0`, and take `N = N_0`.
- The points `g^k v` with `0 ≤ k < N` are distinct and lie in `B(v, K m_N + 1)`. So
  `N ≤ C (K m_N + 1)^d < N`, which is false.
- So `L < N_0` for every `v`, and `g^(lcm(1..N_0))` acts trivially: `g` has finite order in `G`.
- `BS(1,k) = ⟨a, t | t a t^(-1) = a^k⟩`: `t^j a^e t^(-j) = a^(e k^j)`. Write
  `N = Σ_(j ≤ log_k N) e_j k^j` with `0 ≤ e_j ≤ k−1`. Then `a^N = Π_j t^j a^(e_j) t^(-j)` has length
  `≤ Σ_j (2j + k) = O(log^2 N) = o(N^(1/d))`, which is enough.
- `a` has infinite order in `BS(1,k)`, so `BS(1,k)` does not embed.
- For the Callard–Salo element, apply this to the finitely generated subgroup in which
  `|f^N| = O(log^4 N)` and `f` has infinite order (`brin-thompson-mv-contains-a-distortion-element`). ∎

**Step 6 (sharpness; not needed for the claim).**
- `S_L = ⟨a, b^L, c^L⟩` is a subgroup, because `[a, b^L] = c^L` and `c` is central. Its cosets
  are `b^t c^u S_L`, with `t, u` mod `L`.
- `a b^t = b^t a c^(±t)` gives the moves `a:(t,u) ↦ (t, u ± t)`.
- An element `a^s b^t c^u` acting trivially on every `X_L` needs `L | t`, and `L | (s t_0 + u)`
  for all `t_0`, for every `L`. So `s = t = u = 0`, and the family is faithful. `check.py`
  confirms this on all words of length `≤ 6`.
- Its local growth is `≈ 0.72 r^3` (`output.txt`, `L = 4096`, `r ≤ 64`). So Steps 1–3 give nothing
  once the ball bound is cubic.
