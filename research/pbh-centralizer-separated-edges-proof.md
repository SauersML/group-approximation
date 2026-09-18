---
rg: 2
id: pbh-centralizer-separated-edges-proof
kind: route
title: Conjugate one vertex group by the stable letter of the identity-edge HNN over the separating subgroup; for one-sided retracts build the separator in a product through the retraction
target: pbh-amalgams-over-centralizer-separated-edges
requires:
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - boone-higman-type-a-class-closed-under-finite-extensions
  - type-a-action-gives-boone-higman-for-subgroups
  - homogeneous-conjugation-invariants-vanish-on-bs-bases
---

Lane proof (bh-free-49, 2026-09-18), not reviewed.

**Step 0 (the engine).** If `D` is realized in `L ∈ B_A`, then
`G_L = L *_D (D × <s>) = <L, s | s d s^-1 = d (d ∈ D)>` lies in `B_A`. This is
(e) ⟹ (d) of `pbh-coset-wreaths-iff-identity-edge-hnns`, applied to `G = L`, `C = D`.
In `G_L` a word is reducible by Britton's lemma only at a subword `s g s^-1` or
`s^-1 g s` with `g ∈ D`.

**Step 1 (amalgams).** Define `Φ : X *_C Y -> G_L` by `Φ(x) = x` and
`Φ(y) = s y s^-1`. On `C` the two definitions agree, because `C <= D` commutes with `s`.
So `Φ` is a homomorphism. Let `g = z_1 ... z_n` be reduced, `n >= 2`, with letters
alternating between `X \ C` and `Y \ C`. In `Φ(g)` each `Y`-letter `y` sits in
`s y s^-1`, and between two such blocks stands an `X`-letter `x` as `s^-1 x s`.
- `s y s^-1` is a pinch only if `y ∈ D`, but `y ∈ Y \ C` and `Y ∩ D = C`.
- `s^-1 x s` is a pinch only if `x ∈ D`, but `x ∈ X \ C` and `X ∩ D = C`.

So `Φ(g)` is reduced, contains `s`, and is not `1`. Single letters map to nontrivial
elements. Hence `Φ` is injective, and `X *_C Y ∈ B_A` by subgroup closure. []

**Step 2 (HNN).** Define `Φ(w) = w` for `w ∈ W` and `Φ(t) = k s`. Then
`Φ(t) u Φ(t)^-1 = k s u s^-1 k^-1 = k u k^-1 = θ(u)` for `u ∈ U <= D`, so `Φ` is a
homomorphism. In `W *_θ`, a word is reducible only at `t w t^-1` with `w ∈ U` or
`t^-1 w t` with `w ∈ V`. The images are `k s w s^-1 k^-1` and `s^-1 k^-1 w k s`.
- The first is a pinch only if `w ∈ D`, that is `w ∈ W ∩ D = U`.
- The second is a pinch only if `k^-1 w k ∈ D`, that is `w ∈ W ∩ k D k^-1 = V`.
- Subwords `t w t` and `t^-1 w t^-1` become `s (w k) s` and `s^-1 (k^-1 w) s^-1`,
  which are never pinches.

So reduced words with a stable letter map to reduced words with a stable letter, and
`Φ` is injective by Britton's lemma. []

**Step 3 (one-sided retracts).** Let `X <= L_X ∈ B_A` and `m ∈ L_X` with `C_X(m) = C`, and
let `ι : X -> L_X` be the inclusion. Put `L'' = L × L_X ∈ B_A`
(product closure) and embed
- `X` as `X'' = {(x, ι(x)) : x ∈ X}`,
- `Y` as `Y'' = {(y, ι(r(y))) : y ∈ Y}`.

Both maps are injective homomorphisms, and they agree on `C` because `r|_C = id`.
Let `D = C_L(S) × C_{L_X}(m) = C_{L''}(S × {m})`, the centralizer of a finite subset of
`L''`, which is realized in `L''` (take `L' = L''`).
- `X'' ∩ D`: `x ∈ C_L(S)` and `ι(x) ∈ C_{L_X}(m)`. The second condition gives `x ∈ C`,
  and conversely `C` commutes with `S` and with `m`. So `X'' ∩ D` is the image of `C`.
- `Y'' ∩ D`: `y ∈ C_Y(S) = C`, and then `ι(r(y)) = y ∈ C` commutes with `m`. So
  `Y'' ∩ D` is the image of `C`.

Step 1 applies to `X'', Y'' <= L''`. []

**Step 4 (configurations are elliptic).** Let `G` act on its Bass--Serre tree `T`
without inversions. Translation length is homogeneous and conjugation invariant
(`homogeneous-conjugation-invariants-vanish-on-bs-bases`), so an element conjugate to a
proper power of itself has length `0` and is elliptic. So `b` is elliptic, and `c`, which
`b` conjugates to `c^2`, is elliptic too. From `b^-1 c b = c^2` we get
`Fix(c^2) = b^-1 Fix(c)`, and `Fix(c) ⊆ Fix(c^2)`, so `b Fix(c) ⊆ Fix(c)`. Pick a vertex
`y ∈ Fix(c)`. Since `b` is elliptic and there are no inversions, `d(y, by)` is even and
the midpoint of `[y, by]` is fixed by `b`. The segment lies in the subtree `Fix(c)`, so
that midpoint is fixed by both `b` and `c`. So `<b, c>` lies in a conjugate of a vertex
group, and a homomorphism injective on vertex groups is injective on `<b, c>`.

For the groups of items 1--3, the inclusions of `X, Y` (or of `W` and `t -> k`) induce a
homomorphism to `L` that is injective on vertex groups. For `L *_D (D × Z)`, the
retraction `s -> 1` onto `L` is injective on every conjugate of `L`. In both cases a pair
`(b, c)` as in item 4 maps to such a pair in `L`, with the same relations. []
