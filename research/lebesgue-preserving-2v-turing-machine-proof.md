---
rg: 2
id: lebesgue-preserving-2v-turing-machine-proof
kind: route
title: "Read a Jacobian-zero brick table on equal-sided bricks as a Turing-machine local rule, transport Theorem D along the identification, and apply bounded-or-linear growth; the full-shift group sits in the wobbling group of Z, where sublinear distortion is impossible"
target: lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group
requires:
  - nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal
  - turing-machine-groups-contain-distortion-elements
  - cubical-coset-proper-actions-capture-distorted-elements
  - heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs
---

Notation of the target. Elements of `2V` are the homeomorphisms `g` of `C^2` with a finite
partition into bricks `[p_i] × [q_i]` such that `g` maps each `[p_i] × [q_i]` onto `[p_i'] × [q_i']`
by `(p_i α, q_i β) ↦ (p_i' α, q_i' β)`, the image bricks again partitioning `C^2`. On that piece
`c(g) = (|p_i| − |p_i'|, |q_i| − |q_i'|)` (the sign convention plays no role below), so
`J(g) = (|p_i| + |q_i|) − (|p_i'| + |q_i'|)` there. A piece may be refined: replacing
`[p_i] × [q_i]` by the bricks `[p_i s] × [q_i t]` over all words `s, t` of fixed lengths gives a
table of the same element, with the same values of `c`.

**Coordinates.** `Φ(a, b)_i = a_i` for `i ≥ 0` and `Φ(a, b)_i = b_{−1−i}` for `i < 0`. For words
`u, v` of length `r` write `ū` for the reversal of `u`. The point `xu.vy` of `X` (positions
`−r, …, −1` read `u`, positions `0, …, r − 1` read `v`) is `Φ(a, b)` with `a = v y`,
`b = ū x̄`, where `x̄` is the one-sided sequence read leftward from position `−r − 1`. So the cylinder
`{xu.vy : x, y arbitrary}` is `Φ([v] × [ū])`. More generally, for words `u', v'` of any lengths
the string `x u' v' y`, with the origin placed between `u'` and `v'`, is `Φ(v' y, ū' x̄)`.

## Item 1

**`RTM_fix(2,1) ⊆ Φ M_2 Φ^{-1}`.** Let `f ∈ RTM_fix(2, 1)` have radius `r` and local rule
`(u, v) ↦ (u', v')` with `|u'| + |v'| = 2r`. By the coordinates paragraph,
`Φ^{-1} f Φ` maps `(v y, ū x̄) ↦ (v' y, ū' x̄)`. So on the brick `[v] × [ū]` it is the prefix
replacement onto `[v'] × [ū']`. The bricks `[v] × [ū]` with `|u| = |v| = r` partition `C^2`.
`f` is a homeomorphism, so the image bricks are pairwise disjoint and cover `C^2`. Hence
`Φ^{-1} f Φ ∈ 2V`. On each piece `J = (|v| + |ū|) − (|v'| + |ū'|) = 2r − 2r = 0`, so
`Φ^{-1} f Φ ∈ M_2`.

**`Φ M_2 Φ^{-1} ⊆ RTM_fix(2,1)`.** Let `g ∈ M_2`, with a table `[p_i] × [q_i] → [p_i'] × [q_i']`.
`J(g) ≡ 0`, and `J(g)` is constant on each piece, so `|p_i| + |q_i| = |p_i'| + |q_i'|` for all
`i`. Let `r ≥ max_i max(|p_i|, |q_i|)`. Every brick `[v] × [w]` with `|v| = |w| = r` lies in exactly
one `[p_i] × [q_i]`, say `v = p_i s` and `w = q_i t`, and `g` maps it by prefix replacement onto
`[p_i' s] × [q_i' t]`. Here `|p_i' s| + |q_i' t| = |p_i'| + |q_i'| + (r − |p_i|) + (r − |q_i|) = 2r`.
Define the local rule `(u, v) ↦ (u', v')` by `w = ū`, `v' = p_i' s` and `ū' = q_i' t`. By the
coordinates paragraph, `Φ g Φ^{-1}(xu.vy) = x u'.v' y` for all `x, y`. `Φ g Φ^{-1}` is a
homeomorphism, so it lies in `RTM_fix(2, 1)`.

Both inclusions respect composition, since both groups act on the same space. So
`Φ M_2 Φ^{-1} = RTM_fix(2, 1)` as groups, and `M_2 ≅ RTM(2, 1)` by item 1 of
`turing-machine-groups-contain-distortion-elements`. The measure remark in the target is a
consistency check and is not used. Under `Φ`, `λ` becomes the uniform Bernoulli measure on `X`
(cylinders fixing `m` positions have mass `2^{−m}` on both sides). Item 3(a) of
`nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal` says `M_2` is the `λ`-preserving subgroup,
and Barbieri–Kari–Salo's theorem (quoted in `turing-machine-groups-contain-distortion-elements-citation`)
says reversible machines are the measure-preserving ones.

## Item 2

Item 2 of `turing-machine-groups-contain-distortion-elements` (Callard–Salo Theorem D with
`n = 2`, `k = 1`) gives a finitely generated `G = ⟨F_0⟩ ≤ RTM(2, 1)` and `f_0 ∈ G` of infinite
order with `|f_0^N|_{F_0} = O(log^4 N)`. Let `θ : RTM(2, 1) → M_2` be the isomorphism of item 1
(the canonical isomorphism with `RTM_fix(2, 1)`, followed by conjugation by `Φ^{-1}`). Put
`F = θ(F_0)` and `f = θ(f_0)`. An isomorphism carries `⟨F_0⟩` onto `⟨F⟩` and preserves word
lengths, so `|f^N|_F = |f_0^N|_{F_0} = O(log^4 N)`, and `f` has infinite order.

For `n ≥ 2`, `ι(g) = g × id^{n−2}` is an injective homomorphism `M_2 → M_n`
(item 3(d) of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`; for `n = 2` it is the identity).
So `ι(f)` has infinite order and `|ι(f)^N|_{ι(F)} = |f^N|_F`.

## Item 3

(a) Apply item 3 of `cubical-coset-proper-actions-capture-distorted-elements` with `G = M_n` and
`H = 1`. `H` has no element of infinite order, so its hypothesis on `H` holds vacuously. By item 2,
`M_n` has an infinite-order distorted element. So no commensurating action of `M_n` has `ℓ` proper
modulo `1`, that is, proper. An action on a CAT(0) cube complex gives a commensurating action on
the set of half-spaces, with `ℓ(g)` the combinatorial displacement of a vertex (Setting of that
node). A proper action on the complex makes this `ℓ` proper. `RTM(2, 1) ≅ M_2` is the case `n = 2`.

(b) `ι(f)` lies in the finitely generated subgroup `⟨ι(F)⟩` of `nV` with `|ι(f)^N| = o(N)`, so it
is an infinite-order distorted element of `nV`. Item 2 of
`cubical-coset-proper-actions-capture-distorted-elements`, with `G = nV`, gives `ι(f)^d ∈ H`.

(c) Suppose `ψ = ℓ` comes from a commensurating action of `nV` and is proper on `M_n`, that is,
`{g ∈ M_n : ℓ(g) ≤ R}` is finite for every `R`. Restricting the action to `M_n` gives a
commensurating action of `M_n` with the same function `ℓ|_{M_n}`, which is proper. That
contradicts (a). The prerequisite "`M_2` is Haagerup" is the case in which `ψ` is only required to
live on `M_2`, and (a) with `n = 2` excludes wall-count witnesses of it in the same way.

## Item 4

`[[X]] ≤ Φ M_2 Φ^{-1}` is item 3(c) of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`.

**`[[X]]` embeds in the wobbling group of `Z`.** Fix `x* ∈ X` whose `σ`-orbit is dense. Such a
point exists: concatenate all finite words. It is not periodic, since a periodic orbit is finite
and `X` is infinite. For `g ∈ [[X]]`, with `g(x) = σ^{k_g(x)} x` and `k_g` continuous, define
`ρ(g)(m) = m + k_g(σ^m x*)`. Then `g(σ^m x*) = σ^{ρ(g)(m)} x*`. Since `x*` is not periodic,
`ρ(g)(m)` is the unique integer with this property. So
`gh(σ^m x*) = g(σ^{ρ(h)(m)} x*) = σ^{ρ(g)(ρ(h)(m))} x*`, which gives `ρ(gh) = ρ(g) ρ(h)`. Also
`ρ(g^{-1})` inverts `ρ(g)`, so `ρ(g)` is a bijection of `Z`.
- `|ρ(g)(m) − m| ≤ max|k_g| < ∞` (continuity on a compact space). So `ρ(g) ∈ W(Z)`, the
  wobbling group of the graph `Z` with edges `{m, m+1}`.
- If `ρ(g) = id` then `g` fixes every point of the dense orbit. By continuity `g = id`.

So `ρ` is an injective homomorphism `[[X]] → W(Z)`.

**No distortion.** In the graph `Z`, `|B(v, r)| = 2r + 1 ≤ 3r` for all `v` and all `r ≥ 1`. So
item 3 of `heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs` applies with `d = 1` and
`C = 3`. If `L = ⟨S⟩ ≤ W(Z)` is finitely generated and `g ∈ L` has `|g^N|_S = o(N)`, then `g`
has finite order. Apply this to `ρ(L)` for a finitely generated `L ≤ [[X]]`. `ρ` is an
isomorphism onto its image, so word lengths agree, and `[[X]]` has no distorted element.

**The shift-only rules.** An element of `[[X]]` is locally `σ^k` with `|k| ≤ max|k_g|`. Take
`r ≥ max|k_g|` so large that `k_g` is constant on cylinders fixing `[−r, r)`. On such a cylinder
`σ^k(xu.vy)` is the same bi-infinite string `x u v y` with the origin moved by `k`, that is,
`x u'.v' y` with `u'v' = uv` and `|u'| = r + k`. So the local rule of item 1 is a re-cut of `uv`.
Conversely, a rule that is everywhere a re-cut is locally a power of `σ`. This is only the
description quoted in the target, and nothing else uses it.

**Scope.** No step estimates `|f^N|` directly, and none uses the internal structure of the
Callard–Salo element. Everything passes through Theorem D and the exact identification of item 1.
