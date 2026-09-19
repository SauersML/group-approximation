---
rg: 2
id: averaging-fullness-witnesses-force-uniform-expansion-proof
kind: route
title: Count dimensions of the finite windows of a permutation module, pass from means to Følner sets by Namioka, and spread over conjugates by simplicity
target: averaging-fullness-witnesses-force-uniform-expansion
requires:
  - thompson-v-finitely-presented-infinite-simple
  - thompson-v-amenable-actions-are-free-off-fixed-points
---

Notation as in the claim. `F_2[Ω]` is the permutation module, with basis `δ_x` and `g δ_x = δ_(gx)`. It is a
left `F_2[G]`-module, so `c e b` acts as the composite `C E B` of the operators of `c`, `e` and `b`. For
`X ⊆ Ω`, `W_X` is the span of `{δ_x : x ∈ X}`.

**Step 1. The rank of `e` on a window.**
- `E δ_x = δ_x` if `hx = x`.
- Otherwise `E δ_x = σ_O`, the sum over the `h`-orbit `O` of `x`, which has size 3.
- The vectors `σ_O` and `δ_x` for distinct orbits have disjoint supports. So `dim E W_F` is the number
  `N(F)` of `⟨h⟩`-orbits meeting `F`.

Call an orbit of size 3 meeting `F` *partial* if it is not contained in `F`, and let `p` be the number of
partial orbits. Each partial orbit contains a point `x ∈ F` with `hx ∉ F`, so `p <= |F \ h^(-1)F| = |hF \ F|`.
Each partial orbit meets `F` in at least one point. Hence

```text
N(F)  <=  |F ∩ Fix h| + (|F \ Fix h| - p)/3 + p  <=  |F ∩ Fix h| + |F \ Fix h|/3 + (2/3)|hF \ F| .
```

**Step 2. Injectivity of `E B`.**
- `C E B` is the identity, so `E B` is injective and `dim E B W_F = |F|`.
- `B W_F ⊆ W_(S_b F)`.
- `W_(S_b F) ⊆ W_F + W_(S_b F \ F)`, so `dim E W_(S_b F) <= N(F) + |S_b F \ F|`.

Therefore `|F| <= N(F) + |S_b F \ F|`. Substitute Step 1, and use
`|F| = |F ∩ Fix h| + |F \ Fix h|`:

```text
(2/3)|F \ Fix h|  <=  (2/3)|hF \ F| + |S_b F \ F| .
```

That is the Theorem. For `c`, apply the anti-automorphism `* : g ↦ g^(-1)`. Then `b* e* c* = 1`, and
`e* = 1 + h² + h = e`. The support of `c*` is `S_c^(-1)`. `C` was never used beyond being a linear map, so
nothing about `c` is needed.

**Step 3. Følner sets that keep a mean's mass (Day–Mazur–Namioka).**
Let `H` act on `Ω` with an `H`-invariant mean `m`. Let `M ⊆ Ω` with `m(M) = μ > 0`, and let `S ⊆ H` be
finite with `0 < ε < 1`. Then some finite nonempty `F ⊆ Ω` satisfies both

```text
Σ_(s∈S) |sF Δ F| <= ε|F|    and    |F ∩ M| >= (μ/2)|F| .
```

*Day–Mazur.*
- Finitely supported probability vectors `f` are weak*-dense in the means on `ℓ∞(Ω)`, so a net `f_α → m`.
- For every `φ ∈ ℓ∞`, `⟨s f_α - f_α, φ⟩ = ⟨f_α, s^(-1)φ - φ⟩ → m(s^(-1)φ - φ) = 0`. Also `⟨f_α, 1_M⟩ → μ`.
- So the net `((s f_α - f_α)_(s∈S), ⟨f_α, 1_M⟩ - μ)` tends weakly to `0` in `ℓ¹(Ω)^S ⊕ R`.
- By Mazur's theorem, some convex combination `f` of the `f_α` satisfies `Σ_s ||sf - f||_1 < η` and
  `⟨f, 1_M⟩ > μ - η`, for any `η > 0`.

*Namioka.* Put `E_t = {f > t}` for `t > 0`. Each is finite, and `sE_t = {sf > t}`. Then:
- `∫_0^∞ |sE_t Δ E_t| dt = ||sf - f||_1`;
- `∫_0^∞ |E_t| dt = 1`;
- `∫_0^∞ |E_t ∩ M| dt = ⟨f, 1_M⟩`.

Let `φ(t) = |E_t ∩ M| - (μ/2)|E_t| - (μ/2ε) Σ_s |sE_t Δ E_t|`. Then
`∫ φ >= μ - η - μ/2 - (μ/2ε)η`, which is positive for `η` small. So `φ(t) > 0` for some `t`, where `E_t`
is nonempty. For that `t`, `F = E_t` has `|F ∩ M| > (μ/2)|F|` and
`Σ_s |sF Δ F| < (2ε/μ)|F ∩ M| <= (2ε/μ)|F|`. Rescale `ε`.

(This is the standard route. Cornulier, arXiv:1308.1318, Lemma 5.9, records the `ℓ²` form, "has almost
invariant vectors if and only if the G-set X is Eymard-amenable". Only the elementary argument above is
used.)

**Step 4. Corollary 1.**
- Let `m` be an `H_b`-invariant mean on the `G`-set `Ω`, and suppose `μ = m(Ω \ Fix h) > 0`.
- Step 3, with `H = H_b`, `M = Ω \ Fix h` and `S = S_b ∪ {h}`, gives `F` with `|F \ Fix h| >= (μ/2)|F|`
  and `|hF \ F| + |S_b F \ F| <= ε|F|`.
- The Theorem gives `(μ/2)|F| <= (3/2) ε |F|`, which is false for `ε < μ/3`. So `m(Fix h) = 1`.

The listed consequences follow.
- A finite `H_b`-set with its uniform mean gives: `h` acts trivially on it.
- If `K ⊴ H_b`, `h ∉ K` and `Q = H_b/K` is amenable, take `Q` with an invariant mean. The image of `h`
  is a nontrivial element, so it acts freely and `m(Fix h) = 0`. This is impossible.
- `H_b` amenable is the case `K = 1`.
- Residual finiteness of such a `Q` gives a finite quotient in which `h` survives. This is impossible by
  the first point.

**Step 5. Corollary 2.** If `Fix h = ∅`, the Theorem reads `|F| <= |hF \ F| + (3/2)|S_b F \ F|`. Both
terms are at most `|(S_b ∪ {h})F \ F|`, so `|F| <= (5/2)|(S_b ∪ {h})F \ F|`.

**Step 6. Corollary 3.**
- Let `G` be finitely generated, infinite and simple, with `c e b = 1`, and let `m` be a `G`-invariant
  mean on a `G`-set `Ω`.
- For `k ∈ G`, the conjugate `q = k h k^(-1)` has order 3, with `(kck^(-1))(1 + q + q²)(kbk^(-1)) = 1`.
  Since `m` is invariant under all of `G`, Corollary 1 gives `m(Fix q) = 1`.
- `h ≠ 1` and `G` is simple, so the normal closure of `h` is `G`. Each generator `t` in a finite
  generating set `T` is a finite product of conjugates `q_i^(±1)`.
- `Fix t ⊇ ⋂_i Fix q_i`, which has mean 1. So `m(Fix G) = m(⋂_(t∈T) Fix t) = 1`, and `Fix G ≠ ∅`.
- Every nonempty `G`-set with an invariant mean thus has a fixed point, hence a finite orbit. That is
  Cornulier's Definition 1.2 (arXiv:1308.1318): "A locally compact group G has Property FM if for every
  continuous discrete G-set X with a G-invariant mean on all subsets of X, there exists a finite
  G-orbit."

Imports:
- For `V`, `thompson-v-finitely-presented-infinite-simple`.
- For `2V`, Brin, *Higher dimensional Thompson groups*, Geom. Dedicata 108 (2004), arXiv:math/0406046,
  abstract: "Like V it is an infinite, finitely presented, simple subgroup of the homeomorphism group of
  the Cantor set".

Question 1.19(1) of arXiv:1308.1318 reads verbatim: "Consider R. Thompson's groups T and V of the circle
and the Cantor set. Do T and V have Property FM?"

**Step 7. Corollary 4.**
- Let `Ω_0` be a `V`-set without global fixed points, with a `V`-invariant mean `m`.
- Item 2 of `thompson-v-amenable-actions-are-free-off-fixed-points` gives `m(Fix x) = m(Fix V) = 0` for
  every `x ≠ e` in `V`.
- Let `P = (V ⊗ 1)(1 ⊗ V) ≤ 2V`. The two factors commute and meet trivially, so `P ≅ V × V`.
- Let `P` act on `Ω_0` through the first projection. Then `m` is `P`-invariant, and `g ⊗ 1` acts as `g`,
  so `m(Fix(g ⊗ 1)) = 0`.
- To realize this inside a `2V`-set, induce: `Ω = 2V ×_P Ω_0` contains `Ω_0` as a `P`-invariant subset.
  Transfer `m` to `ℓ∞(Ω)` by restricting functions to `Ω_0`.
- If `S_b ⊆ P`, then `H_b ≤ P`, so `m` is `H_b`-invariant with `m(Fix h) = 0`. This contradicts
  Corollary 1. The same applies to `S_c`.
- For the `V` claim the witness lies in `V`, and `Ω_0` itself contradicts Corollary 1 with its own `h`.

