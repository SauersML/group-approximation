---
rg: 2
id: h4-i25-shadow-centre-forms-hold-only-up-to-rotation
kind: claim
title: In the I_2(5) single-flat shadow the Huang-type centre forms y_2 and s_4^k A_Y fail for a fixed base edge, but hold after rotating the hexagon on every tested tuple
distinct_from:
  h4-i25-fibred-shadows-are-rigid-cluster-braid-groups: that identifies the I_2(5) shadow class (A_6 single-edge hexagons with N-letters in N_V); this decides the centre-form question inside that class.
  h4-a2-fibred-shadows-are-a4-pure-braid-retractions: that treats the A_2-flat shadows; this treats the centre forms in the I_2(5) shadows.
---

**Setting.** Notation is as in `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups` and
`h4-case1-pure-normal-form-and-fibred-obstruction`.
- The *class* `𝓗_V` is the set of `A_6` single-edge hexagons for `X'' = {s_1..s_5}`, `Y'' = {s_4,s_5,s_6}`.
  Such a hexagon is a tuple `α_i ∈ F''`, `β_i ∈ N_V` with `∏α_i = ∏β_i = 1` and `α_1β_1α_2β_2α_3β_3 = 1`.
  Its vertices are `x_1 = A_X, x_2 = α_1A_X, x_3 = α_1β_1α_2A_X` and
  `y_1 = A_Y, y_2 = α_1β_1A_Y, y_3 = β_3^{-1}A_Y`.
- `ρ_V(s_4^2) = D = Δ_C^2`, the full twist of the cluster `C` (in `V0`, where `H_{s_4}` is the cluster wall).
  Odd powers of `s_4` do not lie in the single-edge layer and have no `ρ_V`-image there.
- The *base-edge forms* asked for in `h4-case1-pure-normal-form-and-fibred-obstruction` are:
  - **(Y2)** `y_2` is a centre, i.e. adjacent to `x_1`;
  - **(TW)** `D^j A_{Y''}` is a centre for some `j ∈ ℤ`.

  Both depend on the base edge `(x_1, y_1)` chosen for the normal form.

**(1) The base-edge forms fail (NO to the literal question).** Take the `A_3` arc-model tuple
- `α_1 = A_{24}`, `α_2 = A_{34}`, `α_3 = (α_1α_2)^{-1}` in `F = ⟨A_{24}, A_{34}⟩`;
- `β_1 = A_{12}A_{13}`, `β_2 = A_{12}^{-1}`, `β_3 = A_{12}A_{13}^{-1}A_{12}^{-1}` in `N = ⟨A_{12}, A_{13}⟩`.

Push it into `𝓗_V` with the cabling embedding `ι : P_4 → P_7` of the proof, which sends `F → F''`, `N → N_V` and
`A_{12} ↦ D`. The image is a hexagon of `𝓗_V` with these properties:
- its six vertices are distinct and form a 6-cycle;
- **neither base-edge form holds**: `i(y_2, x_1) = 6`, and for every `j ∈ ℤ` the vertex `D^j y_1` is not
  adjacent to `x_3`, since `i(D^j y_1, x_3) ≥ 18|j| − 6 > 0` for `j ≠ 0` and `i(y_1, x_3) = 6`;
- **it still has a centre, namely its own vertex `y_3`**, which is adjacent to `x_1, x_2, x_3`.

The same holds in the `A_3` model, with intersection numbers `2`, `6|j| − 2` and `2`.

So the answer to "does every hexagon of `𝓗_V` have a centre `ρ_V(y_2)` or `ρ_V(s_4^k)A_{Y''}`?" is **no**. This
hexagon is not a counterexample to the bottom-triple claim, and it is not centreless.

**(2) What survives: the forms up to rotation.** Re-base the same hexagon at the edge `(x_2, y_1)`, with the
opposite orientation, using the transport `α_1 ∈ F ⊂ P_Y`. Its new `y_2` is `α_1^{-1}y_3`. So "`y_3` is a
centre" is exactly form (Y2) in the rotated normal form.

The Case 1 target must therefore be stated invariantly:
- **(R)** every hexagon of `𝓗_V` has a centre of form (Y2) or (TW) *for one of its 6 base edges*, each with
  both orientations.

Evidence for (R), all certified in curver:
- 224 exact nondegenerate `A_3` tuples with `|α| ≤ 2`, `|β_1|, |β_3| ≤ 2`: all satisfy a base-edge form at
  `(x_1, y_1)`.
- 180 exact `A_6` tuples in `𝓗_V` at letter length 1: all satisfy a base-edge form.
- The 32 closing `A_3` hexagons with `|α_i| ≤ 2`, `|β_1| ≤ 2` that fail both base-edge forms (their `β_3` has
  length 3): **each has `y_3` as a centre**, so (R) holds. Transported twists at the edges `(x_2,y_2)` and
  `(x_3,y_2)` with `j = −1` also give centres.

**(3) Status of the single-flat programme.**
- The *pair lemma* (open, 1910 tests, 0 violations): in the `A_3` arc model, a puncture lying in the
  `d_1`-region of `x_i ∪ x_j` for each of the three pairs lies in the `d_1`-region of `x_1 ∪ x_2 ∪ x_3`.
  It gives every pure `A_3` hexagon a centre. Through `ι`, which preserves adjacency, the image of that
  centre is a centre of the image hexagon.
- So cabling `A_3` hexagons into `𝓗_V` cannot produce a centreless hexagon. Conditionally on the pair lemma,
  that route to a counterexample is dead.
- Together with (1), the single `I_2(5)` flat shadow shows no sign of a centreless hexagon. The remaining
  question is (R), or the stronger "some centre is a hexagon vertex". A proof of either needs shadows that
  see more than one flat, or non-fibred shadows.

Proof and certificates: `h4-i25-shadow-centre-forms-hold-only-up-to-rotation-proof`.
