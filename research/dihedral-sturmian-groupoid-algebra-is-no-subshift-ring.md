---
rg: 2
id: dihedral-sturmian-groupoid-algebra-is-no-subshift-ring
kind: claim
title: The dihedral Sturmian groupoid algebra LC(X_α×Z/2,F_2)⋊D_∞ is isomorphic to no matrix ring over LC(Y,F_2)⋊Z for any infinite minimal Cantor system Y, so it refutes Cartan uniqueness at no subshift
distinct_from:
  dihedral-cantor-crossed-product-k1-has-exponent-four: that bounds K_1 for any dihedral action whose rotation is minimal; this applies it to the Cartan test object, after proving that the rotation T′ on X_α × Z/2 is minimal
  subshift-crossed-product-algebraic-cartans-are-conjugate: that is the open Cartan-uniqueness question; this settles only its decider (c), negatively, and leaves the question open
  orbit-bijective-cocycle-gives-z-action-groupoid: that shows the dihedral groupoid is not a Z-action groupoid; this shows its Steinberg algebra is not isomorphic to a matrix ring over the algebra of any minimal Z-action groupoid on a Cantor space
artifacts:
  - research/artifacts/dihedral-cantor-k1-exponent-four-2026-09-16.md
---

**Setting.**
- `(X,T)` is an infinite minimal Cantor system, and `R: X → X` is a homeomorphism with `R² = id` and `RTR = T^(−1)`.
- `X′ = X × Z/2`, with `T′(x,e) = (Tx, e+1)` and `s(x,e) = (Rx, e+1)`.
- Then `s² = id` and `sT′s = T′^(−1)`, so `D_∞ = ⟨T′, s⟩` acts on `X′`. Put `G_D = D_∞ ⋉ X′`.

**Statement.**
1. If `T²` is minimal on `X`, then `A_(F_2)(G_D) ≅ LC(X′,F_2) ⋊ D_∞` is not isomorphic to `M_n(LC(Y,F_2) ⋊ Z)`,
   for any `n ≥ 1` and any infinite minimal Cantor system `Y`, in particular any infinite minimal subshift.
2. **(Sturmian case.)** Let `α ∈ (0,1)` be irrational, `X_α ⊆ {0,1}^Z` the closure of the codings
   `x^θ_n = 1_([1−α,1))({θ + nα})`, and `(Rx)_n = x_(−n)` (or any `T^jR`). Then:
   - `(X_α,T)` is an infinite minimal Cantor system;
   - `R` preserves `X_α`, and `R² = id`, `RTR = T^(−1)`;
   - `T²` is minimal.

   So item 1 applies to the dihedral Sturmian groupoid of `research/artifacts/sk-cartan-counterexample-2026-09-13-part1.md` §5.

**Consequence for Cartan uniqueness.** In `subshift-crossed-product-algebraic-cartans-are-conjugate`, decider (c)
asked whether this groupoid algebra, whose model has `Z/2` isotropy and so fails (D1), is some `R_Y`. The answer is no.
This test object gives no counterexample, and the target claim stays open.

**Scope and inputs.**
- The Sturmian facts in item 2 are proved from scratch in artifact §4, Lemma 4b. Uniform recurrence of irrational
  rotations by `α` and `2α` is shown by compactness. Classical Sturmian minimality is not quoted.
- The obstruction is the `K_1` orientation: `K_1 ≅ Z` for the `Z`-crossed product, and `4·K_1 = 0` for the dihedral
  one.
- This excludes only Cartan models with a global orientation-reversing index-two structure (artifact §5,
  Proposition 5). Cartan models whose isotropy does not come from such a structure are not addressed.

Proof in the `-proof` route and artifact §4. Unreviewed.
