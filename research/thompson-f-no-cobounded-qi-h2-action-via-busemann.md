---
rg: 2
id: thompson-f-no-cobounded-qi-h2-action-via-busemann
kind: route
title: The Busemann pseudocharacter dies on the perfect group [F,F], so Hölder makes [F,F] act trivially on the boundary circle
target: thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2
requires:
  - thompson-f-quasimorphisms-vanish-on-f-prime
  - busemann-null-isometries-have-no-boundary-contraction
  - cobounded-qi-h2-actions-without-free-groups-are-focal
  - two-boundary-fixed-points-block-cobounded-qi-h2-actions
  - thompson-f-has-no-free-subgroups
artifacts:
  - research/artifacts/thompson-f-qi-h2-busemann-reduction-2026-09-16.md
---

This route is an alternative to `thompson-f-no-cobounded-qi-h2-action-via-markovic`. It avoids
Markovic's theorem and the Tits alternative. The analytic input is replaced by two things:
- a quasimorphism swindle, `thompson-f-quasimorphisms-vanish-on-f-prime`;
- an elementary estimate on horospherical products, `busemann-null-isometries-have-no-boundary-contraction`.

The other two requirements are classical coarse geometry:
- `cobounded-qi-h2-actions-without-free-groups-are-focal`, which packages non-proper boundary theory
  and Gromov's classification;
- `two-boundary-fixed-points-block-cobounded-qi-h2-actions`, which has the direct route
  `two-boundary-fixed-points-block-via-busemann-projection`.

The argument is Part 3 of the artifact.

**Lemma H (Hölder).** Let `A` be a group of increasing homeomorphisms of `R` in which no non-identity
element has a fixed point. Then `A` is abelian.

*Proof.* If `A` is trivial there is nothing to prove. Otherwise some `f ≠ e` exists, and by step 1
either `f` or `f^{-1}` is positive, so positive elements exist.
1. **Order.** For `f ≠ g` in `A`, `g^{-1}f` has no fixed point, so `f − g` has constant sign on `R`.
   - Setting `g < f` iff `f > g` pointwise gives a total order.
   - It is left-invariant because elements of `A` are increasing. It is right-invariant by
     substitution.
   - Hence `x < y` and `u ≤ v` imply `xu < yv`, and inversion reverses the order.
2. **Archimedean.** If `e < f`, the sequence `f^n(0)` increases without bound: a bounded increasing
   sequence would converge to a fixed point. Likewise `f^{−n}(0) → −∞`.
   - So for every `a ∈ A` there is `m` with `f^m(0) ≤ a(0) < f^{m+1}(0)`, hence `f^m ≤ a < f^{m+1}`.
   - Comparisons can be tested at `0`, because the sign of `f − g` is constant.
3. **Case: there is a least positive element `f`.** Then `e ≤ f^{−m}a < f` forces `a = f^m`. So `A` is
   cyclic.
4. **Case: there is no least positive element.**
   - Every `g > e` has some `k > e` with `k^2 ≤ g`. Choose `e < f < g`. Take `k = f` if `f^2 ≤ g`.
     Otherwise take `k = f^{−1}g`; then `e < k < f`, so `k^2 < fk = g`.
   - Suppose `a, b` do not commute. Swapping the names if needed, `ba < ab`. Put `g := ab(ba)^{−1} > e`, choose `k > e` with `k^2 ≤ g`, and choose `m, n`
     with `k^m ≤ a < k^{m+1}` and `k^n ≤ b < k^{n+1}`.
   - Then `ab < k^{m+n+2}` and `(ba)^{−1} ≤ k^{−m−n}`. So `g < k^2 ≤ g`, a contradiction. ∎

**The argument.** Suppose `F` acts isometrically on a geodesic space `X` quasi-isometric to `H^2`, with
a coarsely dense orbit. Write `∂h` for the induced homeomorphism of `∂X`.

1. **Focal structure.** By `thompson-f-has-no-free-subgroups` and
   `cobounded-qi-h2-actions-without-free-groups-are-focal`, fix `δ` and `o` as there. So `∂X ≅ S^1`,
   `F` fixes `ξ ∈ ∂X`, and some `g ∈ F` has `Fix(∂g) = {ξ, η}` with `η ≠ ξ`.
2. **Pseudocharacter.** Let `Ḡ ≤ Isom(X)` be the image of `F`, and `p: Ḡ → R` the pseudocharacter of
   `busemann-null-isometries-have-no-boundary-contraction`(i) at `ξ`. The composite `F → Ḡ → R` is a
   homogeneous quasimorphism. By `thompson-f-quasimorphisms-vanish-on-f-prime` it vanishes on `F'`.
   So every `k ∈ F'` has `p(k) = 0`, and this value depends only on the powers of `k`.
3. **Orientation.** Fix a homeomorphism `ι: ∂X \ {ξ} → R`.
   - Each `∂k` preserves `∂X \ {ξ}`, so it induces a homeomorphism `k_ι` of `R`.
   - "Increasing or decreasing" is a homomorphism `F' → Z/2`. It is trivial because `F'` is perfect.
   - So `k_ι` is increasing for every `k ∈ F'`.
4. **Elements of `F'` with a fixed point act trivially on `∂X`.** Let `k ∈ F'` with
   `Fix(k_ι) ≠ ∅`, and suppose `k_ι ≠ id`.
   - Take a component `J` of the open set `R \ Fix(k_ι)`. It has at least one finite endpoint `s`,
     which lies in `Fix(k_ι)`; say `J = (s, s')`, the other case being symmetric.
   - `k_ι` permutes the components of `R \ Fix(k_ι)` and fixes `s`. `J` is the only component with left
     endpoint `s`, so `k_ι(J) = J`.
   - `k_ι(t) − t` has constant sign on `J`. Pick `k' ∈ {k, k^{−1}}` with `k'_ι(t) < t` on `J`.
   - For `x ∈ J`, the decreasing sequence `k'^n_ι(x)` stays in `J`, is bounded below by `s`, and
     converges to a fixed point in `[s, x)`. That fixed point must be `s`.
   - Put `â := ι^{−1}(s)` and `x̂ := ι^{−1}(x)`. Then `∂k'^n(x̂) → â` in `∂X \ {ξ}`, hence in `∂X`.
     By item 2 of `cobounded-qi-h2-actions-without-free-groups-are-focal`,
     `(∂k'^n x̂ | â)_o → ∞`.
   - Here `∂k'` fixes `ξ` and `â`, `x̂ ∉ {ξ, â}`, and `p(k') = 0` by step 2. This contradicts
     `busemann-null-isometries-have-no-boundary-contraction`(ii).
   - So `k_ι = id`, and `∂k = id`.
5. **`∂(F')` is trivial.**
   - By steps 3 and 4, `A := {k_ι : k ∈ F'}` is a group of increasing homeomorphisms of `R` whose
     non-identity elements have no fixed point. By Lemma H it is abelian.
   - The map `∂k ↦ k_ι` is an isomorphism `∂(F') → A`, because `∂k` fixes `ξ`.
   - So `∂(F')` is an abelian quotient of the perfect group `F'`, hence trivial.
6. **Second fixed point.**
   - By step 5, `∂(F)` is a quotient of `F/F'`, so it is abelian.
   - Each `∂h` commutes with `∂g`, so it preserves `Fix(∂g) = {ξ, η}`. It fixes `ξ`, so it fixes `η`.
   - Now `two-boundary-fixed-points-block-cobounded-qi-h2-actions` contradicts the coarsely dense
     orbit. ∎

**Scope.** The same proof applies to every group `G` with three properties:
- `G` has no non-abelian free subgroup;
- `[G,G]` is perfect;
- every homogeneous quasimorphism of `G` vanishes on `[G,G]`.

`BS(1,2)`, which does act coboundedly on `H^2`, fails only the perfection hypothesis.
