---
rg: 2
id: thompson-f-two-transitive-gap-endpoints-lie-in-hull-orbits-proof
kind: route
title: Splice at a point of the gap, then read the two gap endpoints as the hull endpoints of the two spliced pairs
target: thompson-f-two-transitive-gap-endpoints-lie-in-hull-orbits
requires:
  - thompson-f-two-transitive-disagreement-sets-are-self-similar
  - thompson-f-two-transitive-hull-endpoints-are-rational
---

Imported statements, verbatim:

- From `thompson-f-two-transitive-disagreement-sets-are-self-similar`:
  (SS1) "`D(ω,ω') = ∅` iff `ω = ω'`";
  (SS3) "If `x ∉ D(ω,ω')`, there is `α ∈ Ω` with
  `D(ω,α) = D(ω,ω') ∩ [0,x)` and `D(α,ω') = D(ω,ω') ∩ (x,1]`";
  (SS7) "`max D(ω,ω') = η(ω,ω')` and `min D(ω,ω') = ξ(ω,ω')`".
- From `thompson-f-two-transitive-hull-endpoints-are-rational`:
  (H3) "`η(ω,ω')` and `ξ(ω,ω')` are rational";
  (H4) "There is a single `F`-orbit `Θ^-` of rational points of `(0,1)`
  containing `η(ω,ω')` for all `ω ≠ ω'`, and a single `F`-orbit `Θ^+`
  containing every `ξ(ω,ω')`."

**Items 1 and 2.** Let `D = D(ω,ω')` and let `(a,b)` be a gap of `D`. Pick
`x ∈ (a,b)`. Then `x ∉ D`, and (SS3) gives `α` with

- `D(ω,α) = D ∩ [0,x) = D ∩ [0,a]`, because `(a,x) ∩ D = ∅`;
- `D(α,ω') = D ∩ (x,1] = D ∩ [b,1]`, because `(x,b) ∩ D = ∅`.

The first set contains `a` and the second contains `b`, so both are nonempty,
and by (SS1) `α ≠ ω` and `α ≠ ω'`. Since `a ∈ D`, `max (D ∩ [0,a]) = a`, so
by (SS7) `a = η(ω,α)`. Likewise `min (D ∩ [b,1]) = b`, so `b = ξ(α,ω')`. By
(H4), `a ∈ Θ^-` and `b ∈ Θ^+`, and by (H3) both are rational.

**Item 3.** Assume `D_0` has empty interior. Let `x ∈ D_0` and `ε > 0`.
`D_0` is perfect (item 6 of the self-similar claim, "no isolated points"), so
some `y ∈ D_0` satisfies `0 < |y - x| < ε`. Say `x < y`; the case `y < x` is
the mirror image. The interval `[x,y]` is not contained in `D_0`, because
`D_0` has empty interior. So some `z ∈ (x,y)` is not in `D_0`. Let `(a,b)` be
the component of `[0,1] ∖ D_0` that contains `z`. It is an open interval,
because `D_0` is closed. Since `x, y ∈ D_0`, we get `x ≤ a < z < b ≤ y`, and
`a, b ∈ D_0` as endpoints of a component of the complement lying inside
`[x,y]`. So `(a,b)` is a gap of `D_0` with `a, b ∈ (x - ε, x + ε)`. By
item 1, `a ∈ D_0 ∩ Θ^-` and `b ∈ D_0 ∩ Θ^+`. As `x` and `ε` were arbitrary,
both sets are dense in `D_0`.

`D_0` is uncountable because it is a nonempty perfect compact set (Step 3 of
`thompson-f-two-transitive-irrational-orbit-colorings-proof` gives the Baire
argument). This remark is not used in the items.
