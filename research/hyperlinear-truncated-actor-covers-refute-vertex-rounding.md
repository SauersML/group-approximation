---
rg: 2
id: hyperlinear-truncated-actor-covers-refute-vertex-rounding
kind: claim
title: If infinitely many truncated presentations of the Kun--Thom actor are hyperlinear and have infinite vertex kernel, then (H1) fails at some actor model
distinct_from:
  kazhdan-cover-models-round-iff-kernel-fixed-mass-one: that decides rounding for finite-dimensional representations of a Kazhdan cover of the vertex alone; this uses tracial models of hyperlinear truncated covers of the whole actor and needs no finite quotient.
  kt-hyperlinear-coset-wreath-forces-nonroundable-vertex: that derives failure of (H1) from a hyperlinear intermediate coset wreath; this derives it from a hyperlinear finitely presented cover of the actor whose vertex relations are not all consequences of its short relations.
  kt-actor-model-with-totally-non-roundable-vertex: that is the open existence of a no-rounding witness; this is a second conditional producer of one, independent of the wreaths.
artifacts:
  - research/artifacts/hs-extension-roundable-part-invariance-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, with `r, d >= 3`.
- `S_G ⊇ F_Γ` is a finite generating set of `G`, `F` the free group on `S_G`, and `G = F/K`.
- `K_L` is the normal closure of the relators of length `<= L`, and `G_L = F/K_L` is the truncated presentation.
  So `q_L : G_L -> G` is a cover and `G_(L+1)` is a quotient of `G_L`.
- `Γ^_L = <F_Γ> <= G_L` and `N_Γ(L) = ker(q_L|Γ^_L)`, the vertex kernel.

**Theorem.** Suppose (H1) holds at every trace-preserving actor model. Then for all large `L`, a hyperlinear
`G_L` has finite vertex kernel.

**Equivalently.** If for infinitely many `L` the group `G_L` is hyperlinear and `N_Γ(L)` is infinite, then
`kt-actor-model-with-totally-non-roundable-vertex` holds (when `gcd(r, q-1) = 1`, through its summand `σ_nr`).

**Corollary (a finitely presented target).** Suppose (H1) holds, and the vertex kernels are infinite for
infinitely many `L`. Then those `G_L` are finitely presented non-hyperlinear groups.
- By `kt-wreath-models-never-round-on-the-vertex`, (H1) already makes the finitely generated wreath `W` not
  hyperlinear.
- Under the hypothesis on the vertex kernels, the conclusion upgrades to finitely presented groups.

**The steps.**
1. **Uniform Kazhdan constant.**
   - `Γ^_L` converges to `Γ` in the space of groups marked by `F_Γ`, so it is Kazhdan for `L >= L_0`
     (`fpbs-shalom-property-t-is-open`).
   - Later `Γ^_L` are quotients of `Γ^_(L_0)`, so a Kazhdan constant `κ_0` of `Γ^_(L_0)` serves for all of them.
2. **(H1) gives (FT) at every threshold.** For every `δ > 0` there are `R, ε` such that every
   `(R, ε)`-almost representation of `G` with near-regular trace admits a genuine `π` of `Γ` and a contraction `x`
   with `||x||_2 >= 1/2` and defect `<= δ` on `F_Γ`.
   - Otherwise the ultraproduct of counterexamples is an actor model.
   - Its rounding, with `x` the coordinate inclusion, meets the bound.
3. **Coordinates of a truncated cover.** Take `L >= 3R` and a trace-preserving `τ : G_L -> U(prod_V M_m)`.
   - For `V`-most `m`, the coordinates of `τ` on words of length `<= R` form an `(R, ε)`-almost representation of
     `G`.
   - The trace is near-regular, since nontrivial elements of `G` lift to nontrivial elements of `G_L`.
4. **An invariant vector.** Apply step 2 with `δ = κ_0/4`. Over `V` this gives `x ≠ 0` with defect
   `<= κ_0/4 < κ_0 ||x||_2` for the exact unitary representation `y -> τ(γ) y π(q_L γ)^*` of `Γ^_L`. By Kazhdan it
   has an invariant vector `ξ ≠ 0`.
5. **Contradiction.** `τ(n)ξ = ξ` for `n ∈ N_Γ(L)`, so `ξ = Eξ`, where `E` is the largest projection fixed by
   `τ(N_Γ(L))`.
   - If `N_Γ(L)` is infinite, then `τ(E) <= 1/m` for every `m`: average over `m` distinct kernel elements and use
     the regular trace.
   - So `E = 0` and `ξ = 0`, a contradiction.

**Reading.**
- **The relation to finite presentation.** It is vacuous if `G` is finitely presented relative to `Γ`, that is,
  if `N_Γ(L) = 1` for large `L`.
  - In the stable range `r >= d + 3`, `G` is finitely presented modulo the unverified `K_2` imports
    (Attempts of `kt-actor-model-with-totally-non-roundable-vertex`). There the statement has no content.
  - At rank 3, including the Lean parameter `(2, 3, 3)`, the vertex is infinitely presented (it retracts onto
    `SL_3(F_q[t])`).
  - A sketch, not proved here: degree shifting by the Laurent torus reduces the Steinberg relations of `Γ` to
    boundedly many relations of `St_3(F_q[Z^d])` with the torus adjoined.
  - If the sketch holds, what remains is whether `K_2(3, F_q[Z^d])` is finitely generated as a module over
    `SL_d(Z)`. It is not decided.
- **Contrast with the finite-dimensional route.** This route asks for hyperlinearity of the truncations. The
  Kazhdan-cover corollary asks instead for finite quotients in which the vertex kernel survives.
- **Model tests.**
  - **Trivial case.** If `G` is finitely presented, every `N_Γ(L)` is eventually trivial. The hypothesis fails and
    nothing is claimed.
  - **Real object.** None is verified. The hypothesis needs an actor that is infinitely presented relative to
    its vertex.
  - **Non-truncated covers are outside the scope.** A fixed cover with central kernel `Z`, such as the Heisenberg
    cover of `rf-kazhdan-group-not-flexibly-hs-stable`, does not converge to its quotient. Its tracial models are
    not models of the quotient.

Derivation: `hyperlinear-truncated-actor-covers-refute-vertex-rounding-proof`.
