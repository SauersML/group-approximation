---
rg: 2
id: hall-quotient-has-a-singularity-free-rational-solenoidal-model
kind: claim
title: Hall's quotient B/C acts faithfully by homeomorphisms without singular points on the rational Cantorization of the compact solenoid-times-circle, while the quadratic cocycle of Abels' overgroup A_p/C has no continuous solenoidal extension
distinct_from:
  abels-quotient-product-form-model-with-one-singular-point: that is the non-compact p-adic model with one singular point at infinity, for A_p/C and for B/C; this compactifies B/C over the adelic solenoid instead, with no singular point at all, and shows the same compactification is impossible for A_p/C.
  compact-skew-products-cannot-carry-divisible-fiber-subgroups: that forbids locally constant cocycles over compact totally disconnected bases; this uses a continuous character cocycle over a connected base and cuts it rationally, which that theorem allows.
  hall-quotient-avoids-v-circle-groups-and-periodic-ends: that excludes V, circle groups and periodic ends; this produces a positive compact model and its Cantorization.
---

**ESTABLISHED** (lane `bh-solvable`, lane proof, elementary; not independently reviewed). No priority
is claimed.

## Setting

- `R = Z[1/p]`. `S_p = (R × Q_p)/R` is the `p`-adic solenoid, with `R` embedded diagonally.
- `χ(x_R, x_p) = x_R − {x_p}` mod 1 is its basic character. Here `{x_p}` is the `p`-adic
  fractional part, and `χ` is well defined because `{γ} ≡ γ` mod 1 for `γ ∈ R`.
- `ι(α) = [(α, 0)]` for `α ∈ R`.
- `E = B/C` is Hall's group, with `a(α), b(β), c(γ), t` as in
  `hall-quotient-avoids-v-circle-groups-and-periodic-ends`.

## Statement

1. **Compact affine model.** On `Y_c = S_p × R/Z` put
   `a(α)(s,θ) = (s + ι(α), θ)`, `b(β)(s,θ) = (s, θ + χ(βs))`, `c(γ)(s,θ) = (s, θ − γ)`, and
   `t(s,θ) = (s/p, θ)`. This is a faithful action of `E` by continuous affine maps.
2. **Rational Cantorization, with no singular points.**
   - Let `L_0 = {[(r,x)] : r ∈ R}` (the dense `Q_p`-leaf) and `L_(β,c) = {θ + χ(βs) = c}`, for
     `β ∈ R` and `c ∈ R/Z`.
   - The regular open sets of `Y_c` bounded by finitely many pieces of `L_0` and of the `L_(β,c)`
     form a countable atomless Boolean algebra `𝔅`, and `E` preserves it.
   - So `E` acts faithfully by homeomorphisms on its Stone space `X̂_E`, a Cantor set.
   - Each element of `E` is one affine map, so relative to the full group of `E ⋉ X̂_E` it has no
     singular points.
3. **Quadratic obstruction for A_p/C.** No continuous map `F: S_p × S_p → R/Z` restricts on the leaf
   `Q_p^2` to the cocycle `(x_1, x_2) ↦ −{x_1x_2}` of `e_23(1)` in the coset model of
   `abels-quotient-product-form-model-with-one-singular-point`. Indeed there is no nonzero continuous
   biadditive map `S_p × S_p → R/Z` at all. So the adelic compactification carries Hall's linear
   (character) cocycles but not the quadratic cocycle that Abels' finitely presented overgroup needs.

## Proof

1. **Well defined and continuous.** `ι(α)` translates the compact group, `s ↦ s/p` is an
   automorphism, and `χ(βs)` is continuous in `s`.
   - **Relations.** `a(α)b(β)a(α)^{-1}` sends `θ` to `θ + χ(βs) − χ(βι(α)) = θ + χ(βs) − αβ`, so
     `[a(α), b(β)] = c(αβ)`, and `c(1) = id`. Also `ta(α)t^{-1} = a(α/p)` and `tb(β)t^{-1} = b(pβ)`.
     So this is an action of `E`.
   - **Faithful.** `E` has monolith `⟨c(1/p)⟩`
     (`abels-quotient-product-form-model-with-one-singular-point`, item 5), which acts as a nonzero
     rotation.
2. **The Boolean algebra is invariant.**
   - `L_0` is invariant, since `[(r,x)] = [(0, x − r)]`, `ι(α)` shifts `r` by `α`, and `t` scales it.
   - The family `{L_(β,c)}` is permuted: `b(β')` sends `L_(β,c)` to `L_(β−β',c)`, `a(α)` sends it
     to `L_(β, c+αβ)`, and `t` sends it to `L_(pβ,c)`.
   - In local charts (real interval × `Z_p`-ball × circle interval), these sets are
     polygons in `(s_R, θ)` with sides of slopes in `R` and endpoints in `R`, times `p`-adic balls.
     They form a countable atomless algebra.
   - An automorphism of `𝔅` induces a homeomorphism of its Stone space. The action on `𝔅` is
     faithful because the rational sets separate points of a dense subset of `Y_c`.
3. **No extension.**
   - **Biadditive maps.** For fixed `s_1`, `s_2 ↦ B(s_1,s_2)` is a character of `S_p`, an element of
     the discrete dual `R`. A continuous map from the connected `S_p` to a discrete set is
     constant, so `B = B(0, ·) = 0`.
   - **The specific cocycle.** On the leaf, `x_1 ↦ x_1 + α` is the real translation by `−α`, since
     `[(0, x_1+α)] = [(−α, x_1)]`. Continuity of `F` in the real direction would force
     `{α x_2} → 0` as `α = p^{-k} → 0` in `R`.
   - For `x_2 = Σ_(i ≥ 0) p^(2i)`, the fractional part `{p^{-k}x_2}` tends to `1/(p^2 − 1) ≠ 0`
     mod 1 along even `k`. This value lies in `(0, 1/2)` for every prime `p`. ∎

## Consequences

- **The candidate base, checked.**
  - For `E`: the compact adelic model needs no singular points. `E` lies in the topological full group
    `[[E ⋉ X̂_E]]`, which is a finite germ extension of itself with empty singular set.
  - For `A_p/C`: the solenoidal compactification of the coset model is not an action by
    homeomorphisms (item 3). So Abels' overgroup keeps its single cusp at `∞`
    (`abels-quotient-product-form-model-with-one-singular-point`), and no compact adelic model of
    that form exists.
- **What Boone–Higman for Hall's group now needs.** Finite presentation of a full group carrying
  `E ⋉ X̂_E`, for example `[[E ⋉ X̂_E]]` itself or its product with the Cuntz groupoid
  (`fp-v-times-minimal-action-full-groups-have-type-a-actions` then gives type (A)). `E` is amenable,
  so by the carrier principle of the synthesis (`gq-bh-synthesis-master-route`) a non-amenable
  enlargement of the acting group is expected to be needed. This is a Track A instance with a
  soluble input and a rationally cut, non-subshift unit space.

## Lesson for general BH

Linear cocycles compactify over adelic solenoids, and quadratic ones do not.
- A character cocycle `χ(βs)` is continuous on the solenoid, so Hall's divisible centre can be
  carried with no singular point at all, and a rational Cantorization turns the model into a Cantor
  action by global affine maps.
- The finitely presented overgroup of Abels needs a quadratic cocycle, and quadratic cocycles have no
  continuous extension, because the connected solenoid has only discrete duals.
- So compactness and finite presentation pull the soluble minimax inputs apart. The compact
  singularity-free model belongs to the non-fp input, and the fp overgroup keeps a cusp.
- A host must reconcile them: a finitely presented full group over the compact rational model, or a
  germ host over the cusp.
