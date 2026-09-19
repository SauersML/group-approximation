---
rg: 2
id: quaternary-cantor-set-passes-disagreement-shape-tests-proof
kind: route
title: Interpolate dyadic affine maps on disjoint intervals by elements of F, then check each shape condition on cylinders of the quaternary Cantor set
target: quaternary-cantor-set-passes-disagreement-shape-tests
requires: []
---

The notation is that of the target claim. An element of `F` is affine, of the
form `x ↦ 2^k x + d` with `d ∈ Z[1/2]`, on each interval between consecutive
breakpoints. So it maps `Z[1/2]` to itself and has well-defined one-sided
slopes everywhere.

**Fact DI** (Cannon–Floyd–Parry, Lemma 4.2). Let `[a,b]` and `[c,d]` be
nondegenerate intervals with dyadic endpoints. Then some increasing piecewise
linear homeomorphism `[a,b] → [c,d]` has finitely many breakpoints, all
dyadic, and slopes in `2^Z`.

*Proof.* Choose `n` with `a, b, c, d ∈ 2^{-n} Z`. Then `[a,b]` is a union of
`p` standard intervals `[j2^{-n}, (j+1)2^{-n}]` and `[c,d]` of `q`. Halving
one standard interval raises the count by one and keeps every piece of the
form `[j2^{-m}, (j+1)2^{-m}]`. So both can be cut into `max(p,q)` such pieces.
Map the `i`-th piece of `[a,b]` affinely onto the `i`-th piece of `[c,d]`.
Each of these maps has slope in `2^Z`, and all breakpoints are dyadic. ∎

**Lemma IL (interpolation).** Let `J_1 < … < J_m` be pairwise disjoint compact
intervals in `(0,1)`, possibly degenerate. Let `ψ_1, …, ψ_m` be increasing
dyadic affine maps with `ψ_1(J_1) < … < ψ_m(J_m)`, all contained in `(0,1)`.
Then there is `f ∈ F` that equals `ψ_j` on a neighbourhood of `J_j` for every
`j`.

*Proof.* Dyadic rationals are dense, and the `ψ_j` are continuous. So we can
choose dyadic `c_j < min J_j` and `e_j > max J_j` for which the intervals
`[c_j, e_j]` are pairwise disjoint and ordered in `(0,1)`, and so are their
images `ψ_j([c_j,e_j])`. The points `ψ_j(c_j)` and `ψ_j(e_j)` are dyadic.

- Put `f = ψ_j` on `[c_j, e_j]`.
- Using Fact DI, map `[0,c_1]` onto `[0,ψ_1(c_1)]`.
- Map each `[e_j, c_{j+1}]` onto `[ψ_j(e_j), ψ_{j+1}(c_{j+1})]`.
- Map `[e_m, 1]` onto `[ψ_m(e_m), 1]`.

All of these intervals are nondegenerate and have dyadic endpoints. The result
is an increasing piecewise linear homeomorphism of `[0,1]` with finitely many
dyadic breakpoints and slopes in `2^Z`, which is an element of `F`. ∎

**Corollary O.** If `ψ` is dyadic affine and `x, ψ(x) ∈ (0,1)`, then
`ψ(x) ∈ F·x`. In particular:

- `7/12 = (1/3)/4 + 1/2 ∈ Θ^-`;
- `ψ(Θ^-) ∩ (0,1) ⊆ Θ^-`;
- `f(Θ^±) = Θ^±` for `f ∈ F`.

*Proof.* Apply IL with `J_1 = {x}`. ∎

**Cylinders.** For a binary word `w = w_1 … w_n` put `a_w = Σ_{i≤n} w_i 4^{-i}`
and

`τ_w(x) = 4^{-n}(x - 1/2) + 1/2 + a_w/4`,   `K_w = τ_w(K)`.

Each `τ_w` is dyadic affine, with slope `4^{-n}` and translation
`1/2 - 4^{-n}/2 + a_w/4 ∈ Z[1/2]`. Writing `x = 1/2 + c/4` with `c ∈ C`, we
get `τ_w(x) = 1/2 + (a_w + 4^{-n}c)/4`. So `K_w` is the set of points of `K`
whose first `n` digits are `w`. Its hull is

`H_w = [1/2 + a_w/4, 1/2 + a_w/4 + 4^{-n}/12]`,   of length `4^{-n}/12`.

The following hold for all `w`:

- `K_w = K_{w0} ⊔ K_{w1}`, and `max H_{w0} = 1/2 + a_w/4 + 4^{-n-1}/12` is
  less than `min H_{w1} = 1/2 + a_w/4 + 4^{-n-1}/4`;
- `K = ⊔_{|w|=n} K_w` for every `n`, with the hulls `H_w`, `|w| = n`,
  pairwise disjoint and ordered lexicographically;
- `K = ∩_n ∪_{|w|=n} H_w`.

The digit map `{0,1}^N → K` is a homeomorphism, so `K` is a Cantor set. The
cylinders `K_w` form a basis of clopen sets of `K`.

**Lemma P (prefix codes).** Let `u_1 < … < u_M` be a finite complete prefix
code in lexicographic order, meaning every infinite binary word has exactly one
`u_i` as a prefix. Then `K = K_{u_1} ⊔ … ⊔ K_{u_M}`, and the hulls satisfy
`H_{u_1} < … < H_{u_M}`. Two examples are the empty word for `M = 1` and
`{0, 10, 110, …, 1^{M-2}0, 1^{M-1}}` for `M ≥ 2`.

*Proof.* The partition follows from the digit description of `K_w`. The order
of the hulls follows from the first bullet above, applied at the first letter
where `u_i` and `u_j` differ. ∎

**Item 1, `⊆`.** Let `f ∈ F`, with breakpoints `b_1, …, b_r`, all dyadic.
Fix one `b = b_i`.

- If `b ∉ K`, then `b ∉ ∪_{|w|=n} H_w` for large `n`.
- If `b ∈ K`, then `b` is dyadic, so `b = 1/2 + c/4` with `c ∈ C ∩ Z[1/2]`. A
  base-4 expansion with digits in `{0,1}` never ends in `3333…`, so it is the
  unique expansion of `c`. Since `c` is dyadic, its digits are eventually `0`,
  say from place `m+1` on. For `n ≥ m`, `b` lies in exactly one hull `H_w`
  with `|w| = n`, and there `b = τ_w(1/2) = min H_w`.

So for large `n`, no breakpoint of `f` lies in the interior of any `H_w` with
`|w| = n`. Then `f` is affine and dyadic, `f = φ_w`, on each such `H_w`. Hence
`fK = ⊔_{|w|=n} φ_w τ_w(K)`, a finite union of disjoint dyadic affine copies
of `K` in `(0,1)`.

**Item 1, `⊇`.** Let `D = ψ_1(K) ∪ … ∪ ψ_m(K)`, with the pieces pairwise
disjoint and contained in `(0,1)` and each `ψ_j(x) = 2^{k_j} x + d_j` dyadic
affine. Such a map is increasing.

The pieces are pairwise disjoint compact sets, so they are at distance at
least some `δ > 0` from one another. Take `n` with `2^{k_j} 4^{-n}/12 < δ`
for all `j`. Then the hulls `ψ_j(H_w)`, `|w| = n`, are:

- pairwise disjoint within one `j`, by the cylinder facts;
- disjoint across different `j`, because each hull has length `< δ` and meets
  its own piece.

List these `M = m·2^n` sets `ψ_j τ_w(K)` in increasing order of hulls as
`φ_1(K) < … < φ_M(K)`, with `φ_i = ψ_j τ_w`. Let `u_1 < … < u_M` be the
prefix code of Lemma P. Apply IL with `J_i = H_{u_i}` and the dyadic affine
maps `φ_i τ_{u_i}^{-1}`. Both families are ordered and disjoint, the images lie
in `(0,1)`, and inverses and composites of dyadic affine maps are dyadic
affine. The resulting `f ∈ F` satisfies

`fK = ⊔_i f(K_{u_i}) = ⊔_i φ_i(K) = D`. ∎

**Item 2.** Let `D = ⊔_j ψ_j(K) ∈ 𝒦` (item 1) and let `A ⊆ D` be nonempty and
relatively clopen. Each `A_j = ψ_j^{-1}(A ∩ ψ_j(K))` is clopen in `K`, hence
compact. It is a union of basic cylinders, hence a finite union of them.
Cylinders are nested or disjoint, so after refining to a common level it is a
disjoint union `⊔ K_w`. Then `A = ⊔_j ⊔_w ψ_j τ_w(K)` is a finite disjoint
union of dyadic affine copies of `K` in `(0,1)`, so `A ∈ 𝒦` by item 1.

If `D, D' ∈ 𝒦` are disjoint, then concatenating their two families from item 1
gives a finite family of pairwise disjoint dyadic affine copies with union
`D ∪ D'`. So `D ∪ D' ∈ 𝒦` by item 1. ∎

**Item 3.** Each `fK` is the image of the Cantor set `K` under a homeomorphism
of `[0,1]`, and `K ⊂ (0,1)` gives `fK ⊂ (0,1)`. A Cantor set in the line is
compact, perfect and totally disconnected with more than one point, so it is
not connected, and it has empty interior. ∎

**Item 4.** Let `D = fK` with `f ∈ F`. Then `f` is increasing and maps
`Z[1/2] ∩ (0,1)` to itself, and `f(Θ^-) = Θ^-`.

- `min D = f(1/2) ∈ Θ^+`.
- `max D = f(7/12) ∈ Θ^-`, by Corollary O.
- `min D < max D`.

The gaps of `D` are the images under `f` of the gaps of `K`. Let `(a,b)` be a
gap of `K`. Hull lengths tend to `0`, so there is a largest `n` for which `a`
and `b` lie in one cylinder `K_w` with `|w| = n`. Then `a ∈ K_{w0}` and
`b ∈ K_{w1}`, because `K_w = K_{w0} ⊔ K_{w1}` and `a < b`.

- Every `y ∈ K_{w0}` satisfies `y < min H_{w1} ≤ b`. So `(a,b) ∩ K = ∅`
  forces `a = max K_{w0} = τ_{w0}(7/12)`, which lies in `Θ^-` by Corollary O.
- Likewise `b = min K_{w1} = τ_{w1}(1/2)`, which is dyadic, so `b ∈ Θ^+`.

Applying `f` gives the gap statement for `D`. For density, every nonempty
relatively open subset of `D` contains some `f(K_w)`. That set contains the gap
`f((max K_{w0}, min K_{w1}))`, whose endpoints lie in `Θ^-` and in `Θ^+`. ∎

**Item 5.** Take the two complete prefix codes, in lexicographic order,

`s = (0, 100, 1010, 1011, 11)`,   `t = (00, 01, 10, 110, 111)`.

Apply IL with `J_i = H_{s_i}` and `ψ_i = τ_{t_i} τ_{s_i}^{-1}`. The images
`ψ_i(H_{s_i}) = H_{t_i}` are ordered and disjoint by Lemma P. We get
`f_0 ∈ F` with `f_0 K = ⊔_i K_{t_i} = K`.

- Near `1/2 = min H_0`, `f_0 = τ_{00} τ_0^{-1} : y ↦ 1/2 + (y - 1/2)/4`.
  This fixes `1/2` with slope `1/4` on both sides.
- Near `7/12`, `f_0 = τ_{111} τ_{11}^{-1}`. This has slope
  `4^{-3}/4^{-2} = 1/4`, and it fixes `7/12` because
  `max H_{1^n} = 1/2 + (1/3)(1 - 4^{-n})/4 + 4^{-n}/12 = 7/12` for every `n`.

For `D = gK`, put `f = g f_0 g^{-1}`. Then `fD = D`, and `f` fixes
`g(1/2) = min D` and `g(7/12) = max D`. Near a fixed point `p` of `f_0`, the map
`f_0` is affine with slope `1/4` and preserves each side of `p`. Conjugating by
`g` multiplies each one-sided slope by `α α^{-1}`, where `α` is the slope of
`g` on the same side. So both one-sided slopes of `f` at `g(p)` are
`1/4`. ∎

**Conditions (S1)–(S6).**

- (S1) is items 3 and 1: `𝒦 = F·K` is one orbit.
- (S2) and (S3) are item 2.
- (S4) and (S5) are item 4.
- (S6) is item 5.

Empty interior is item 3. `Θ^+` and `Θ^-` are orbits of rational points, and
they are distinct, because `Θ^-` contains no dyadic point: `F` preserves
`Z[1/2]` and `1/3 ∉ Z[1/2]`.
