---
rg: 2
id: lifted-thompson-t-convex-line-walls-contraction-proof
kind: route
title: Contract a rectangle of arcs onto two different corners, then split walls on the line by winding class
target: lifted-thompson-t-convex-line-walls-are-trivial
requires: []
---

**Conventions.**
- `T` is the group of orientation-preserving homeomorphisms of `S^1 = R/Z` that are
  piecewise linear with finitely many breakpoints, all at dyadic rationals, and whose slopes
  are powers of `2`.
- `T̄` is the group of lifts of elements of `T` to `R`. Every `g ∈ T̄` is an increasing
  homeomorphism with `g(t + n) = g(t) + n` for all `n ∈ Z`. Write `ḡ ∈ T` for its image, and
  `z(t) = t + 1`.
- A *dyadic arc* is a closed arc `[a, a + ℓ] ⊂ S^1` with `a` and `ℓ ∈ (0,1)` dyadic.

**Step 0: dyadic intervals are PL-equivalent.** Let `[p,q]` and `[p',q']` have dyadic endpoints.
Then there is an increasing homeomorphism `[p,q] → [p',q']` that is PL with dyadic breakpoints
and power-of-2 slopes.
- Choose `n` with `2^n(q − p) = k` and `2^n(q' − p') = j`, both integers. Affine maps
  `t ↦ 2^n (t − p)` have slope a power of `2` and dyadic translation. So it suffices to map
  `[0,k]` to `[0,j]`.
- For `k ≥ 2`, the map equal to `t ↦ t/2` on `[0,2]` and to `t ↦ t − 1` on `[2,k]` sends
  `[0,k]` onto `[0,k−1]`. Its only breakpoint is `2`.
- Composing these maps and their inverses reaches any `j ≥ 1`.

**Step 1: contracting elements.** Let `A = [a, a+ℓ]` and `B = [b, b+m]` be disjoint dyadic
arcs, met in the cyclic order `A, C, B, D`, where `C = [a+ℓ, b]` and `D = [b+m, a]` are the gaps.
For `c ∈ {0, ℓ/2}` define `g_c` piece by piece:
- on `A`, `g_c(t) = a + c + (t − a)/2`, which maps `A` onto `A_c = [a+c, a+c+ℓ/2] ⊂ A`;
- on `B`, `g_c(t) = b + (t − b)/2`, which maps `B` onto `B' = [b, b+m/2] ⊂ B`;
- on `C`, a Step-0 map from `C` onto `[a+c+ℓ/2, b]`;
- on `D`, a Step-0 map from `D` onto `[b+m/2, a+c]`.

These arcs have dyadic endpoints. The images again occur in the cyclic order
`A_c, C', B', D'` and fit together at their endpoints. So `g_c` is an orientation-preserving
dyadic PL homeomorphism of `S^1`, that is, `g_c ∈ T`.

On `A`, the map `g_c` is affine with slope `1/2` and fixed point `α_c = a + 2c`, so `α_0 = a`
and `α_(ℓ/2) = a + ℓ`. On `B` its fixed point is `β = b`. Hence
```text
g_c^n(A) = arc of length ℓ/2^n containing α_c,    ∩_n g_c^n(A × B) = {(α_c, β)}.
```

**Step 2: part (1), pairs.** Let `ν` be a `T`-invariant Radon measure on `U`, with `T` acting
diagonally. `A × B` is compact in `U`, so `ν(A × B) < ∞`.
- Since `g_c(A × B) ⊂ A × B` and `ν(g_c E) = ν(E)`, the sets `g_c^n(A × B)` decrease and all
  have the same finite measure.
- By continuity from above, `ν(A × B) = ν{(α_c, β)}` for both values of `c`.
- The points `(a, b)` and `(a+ℓ, b)` of `A × B` are distinct, so
  `ν(A × B) ≥ ν{(a,b)} + ν{(a+ℓ,b)} = 2ν(A × B)`. Hence `ν(A × B) = 0`.

Every point `(s,t) ∈ U` lies in the interior of such a rectangle: take small disjoint dyadic
arcs around `s` and around `t`. There are countably many of them, so `ν(U) = 0`.

For `S^1`: a `T`-invariant Radon measure on the compact space `S^1` is finite. Apply the same
argument to one dyadic arc `A` with `ℓ < 1/2`, using the restriction of `g_c` to `A`. This gives
`ν(A) = ν{a} = ν{a+ℓ}`, hence `ν(A) = 0`, and `S^1` is covered by finitely many such arcs.

**Step 3: index space of convex walls.** A wall `{h, R \ h}` with `h` order-convex and
`∅ ≠ h ≠ R` is one of three kinds.
- *Cuts.* One side is `(−∞, x)` and the other is `[x, ∞)`, or one side is `(−∞, x]` and the
  other is `(x, ∞)`. Index them by `W_cut = R × {o, c}`.
- *Points.* One side is `{x}`. Index them by `W_pt = R`.
- *Intervals.* One side is bounded, with endpoints `x < y` and each end open or closed. Index
  them by `W_int = P × {o,c}²`, where `P = {(x,y) : x < y}`.

This covers everything: if both sides are unbounded, then both are half-lines, and the wall is a
cut. An increasing homeomorphism `g` maps a convex set to a convex set with endpoints `g x` and
`g y` and the same end types. So `T̄` acts on each index space through the coordinates.

The wall pseudometric is `d(p,q) = μ(S(p,q))`, where `S(p,q)` is the set of walls separating
`p` from `q`. It is finite by hypothesis.

**Step 4: the measure is Radon off the points.**
- *Cuts.* For `p < q`, every cut at a point `x ∈ (p,q)` separates `p` from `q`, whatever its
  end type. So `μ_cut((p,q) × {o,c}) ≤ d(p,q) < ∞`, and `μ_cut` is Radon on `W_cut`.
- *Intervals.* Let `a_1 < a_2 < b_1 < b_2`. Take any convex `h` with `inf h = x ∈ (a_1,a_2)`
  and `sup h = y ∈ (b_1,b_2)`, of any end types. Then `a_1 ∉ h`, since `a_1 < x`. And `a_2 ∈ h`,
  since `x < a_2 < b_1 < y`. So `h` separates `a_1` from `a_2`, and the open rectangle
  `(a_1,a_2) × (b_1,b_2)` has `μ_int`-measure at most `d(a_1,a_2)`, for each end type. Finitely
  many such rectangles cover any compact subset of `P`, so `μ_int` is Radon on `W_int`.

**Step 5: winding classes.** For `(x,y) ∈ P` put `w(x,y) = ⌊y − x⌋ ≥ 0`. Let `g ∈ T̄` and
`n = w(x,y)`.
- From `x + n ≤ y < x + n + 1` and `g(t + n) = g(t) + n`, we get
  `g x + n ≤ g y < g x + n + 1`. So `w` is `T̄`-invariant.
- Each `P_n = {w = n}` splits into the invariant pieces `D_n = {y − x = n}` (for `n ≥ 1`) and
  `P_n° = {n < y − x < n + 1}`.
- The map `(x,y) ↦ (x mod 1, y mod 1)` induces equivariant homeomorphisms
  `P_n°/⟨z⟩ ≅ U` and `D_n/⟨z⟩ ≅ S^1`. On `D_n` only the first coordinate matters; `z` acts by
  `(x,y) ↦ (x+1, y+1)`, freely and properly, and `T̄` acts through `T`.
- `W_cut/⟨z⟩ ≅ S^1 × {o,c}` in the same way.

**Step 6: descent of measures.** Let `Y` be one of `W_cut`, `P_n° × {o,c}²` or
`D_n × {o,c}²`, with a `T̄`-invariant Radon measure `μ_Y`. Let `F = {x ∈ [0,1)}` be the
fundamental domain for `⟨z⟩`, and define `ν(E) = μ_Y(π^(-1)E ∩ F)` on the quotient.
- *`ν` is Radon.* If `K` is compact in the quotient, then `π^(-1)K ∩ {x ∈ [0,1]}` is compact.
  For `P_n°`, this holds because `y − x mod 1` stays in a compact subset of `(0,1)` when `K`
  avoids the diagonal.
- *`ν` is `T`-invariant.* Let `g ∈ T̄` and let `Ẽ = π^(-1)E`, which is `z`-invariant. Then
  ```text
  ν(ḡ E) = μ_Y(g Ẽ ∩ F) = μ_Y(Ẽ ∩ g^(-1) F),
  ```
  and `g^(-1)F = {x ∈ [u, u+1)}` with `u = g^(-1)(0)`. Cut this set at the integer `⌈u⌉`. The
  piece with `x ≥ ⌈u⌉` is `z^(⌈u⌉)` of `{x ∈ [0, u+1−⌈u⌉)}`. The other piece is
  `z^(⌈u⌉−1)` of `{x ∈ [u+1−⌈u⌉, 1)}`. Since `z` preserves `μ_Y` and `Ẽ`,
  `μ_Y(Ẽ ∩ g^(-1)F) = μ_Y(Ẽ ∩ F) = ν(E)`.

By Step 2, `ν = 0`. Since `μ_Y(π^(-1)E ∩ z^k F) = ν(E)` for every `k`, it follows that
`μ_Y = 0`. So `μ_cut = 0` and `μ_int = 0`, which is the first bullet of (2).

**Step 7: what is left.** For `p ≠ q`, the point wall at `x` separates `p` from `q` exactly
when `x ∈ {p, q}`. So `d(p,q) = μ{p} + μ{q}`. The point measure is `T̄`-invariant, so
`μ{g p} = μ{p}`. Hence `ψ_p(g) = d(p, g p)` is `2μ{p}` when `g p ≠ p`, and `0` otherwise.
That is the rest of (2).

For (3):
- If `π : X → R` is equivariant and the walls of `X` are `π`-preimages, then walls separate
  `a, b ∈ X` exactly when they separate `π a` from `π b`. So `d_X(a,b) = d(π a, π b)`, which is
  bounded by (2).
- If the walls of `X` are indexed equivariantly by `W_cut ⊔ W_int` through a `T̄`-invariant
  measure that is finite on compact sets, then Steps 5 and 6 apply to that measure directly, and
  it vanishes.
