---
rg: 2
id: thompson-t-co-amenable-bounded-euler-powers-proof
kind: route
title: "Transfer through the invariant mean makes restriction injective on bounded cohomology; the translation-number defect represents e_b; Hartnick-Ott and Amontova-Bucher kill the squares in cases B3-B4"
target: thompson-t-co-amenable-subgroups-see-all-bounded-euler-powers
requires:
  - thompson-f-bounded-cohomology-vanishes-separable-duals
---

Notation is as in `thompson-t-co-amenable-subgroups-see-all-bounded-euler-powers`. Cochains are
real valued. `δ` is the standard coboundary, in homogeneous form on `Γ^{n+1}` or in
inhomogeneous form `(δf)(γ, η) = f(η) − f(γη) + f(γ)` on `Γ²`.

**Imported theorems (literature, cited).**
- **[FFLM]** Fournier-Facio, Löh, Moraschini, *Bounded cohomology and binate groups*,
  arXiv:2111.04305. Together with **[Mo]** Monod, *Lamplighters and the bounded cohomology of
  Thompson's group*, arXiv:2112.13741, this gives `H^*_b(T; R) ≅ R[e_b]`. It also gives the
  bounded acyclicity of `F` used in (B1), which is the ESTABLISHED import
  `thompson-f-bounded-cohomology-vanishes-separable-duals`.
- **[GS]** Ghys–Sergiescu (Comment. Math. Helv. 62, 1987): `H^*(T; Q) ≅ Q[α, χ]/(αχ)`, where `χ`
  is the Euler class, so `e_R^n ≠ 0` for every `n`. This is only a second, independent route to
  step 2.
- **[HO]** Hartnick–Ott, *Bounded cohomology via partial differential equations, I*,
  arXiv:1310.4806, Theorem 1.1: `H^4_cb(G; R) = 0` for every connected Lie group `G` locally
  isomorphic to `SL_2(R)`.
- **[AB]** Amontova–Bucher, Forum Math. 34 (2022), Theorem A, read as stated in Hofmann,
  arXiv:2407.17034. On a free group, the cup product of the class `[δφ]` of a `Δ`-decomposable
  (in particular Brooks) quasimorphism with any bounded class vanishes.
- **[Gr]** Gromov's mapping theorem: a surjection with amenable kernel induces an isometric
  isomorphism in bounded cohomology.
- **[Gh]** Ghys (1987): semi-conjugate circle actions have the same bounded Euler class. This is
  used only for (B3').

## Step 1. Co-amenable restriction is injective in bounded cohomology

Let `m` be a `T`-invariant mean on `ℓ^∞(T/H)`.

The homogeneous complex `ℓ^∞(T^{n+1})` is a strong, relatively injective resolution of `R` for
every subgroup of `T`. This is the standard fact that `ℓ^∞(Γ^{n+1})` restricted to `H ≤ Γ`
remains relatively injective, because `Γ` is a free `H`-set.
- So `ℓ^∞(T^{n+1})^H` computes `H^*_b(H)`, and `ℓ^∞(T^{n+1})^T` computes `H^*_b(T)`.
- Restriction is induced by the inclusion `ℓ^∞(T^{n+1})^T ⊂ ℓ^∞(T^{n+1})^H`.

Define the transfer as follows. For `f ∈ ℓ^∞(T^{n+1})^H` and `t ∈ T^{n+1}`:
- The function `gH ↦ f(g^{-1}t)` is well defined on `T/H`, because
  `f((gh)^{-1}t) = f(h^{-1}·g^{-1}t) = f(g^{-1}t)` by `H`-invariance. It is bounded by `‖f‖_∞`.
- Put `τf(t) = m(gH ↦ f(g^{-1}t))`.

Its properties:
- **`T`-invariant.** For `k ∈ T`, `τf(kt) = m(gH ↦ f((k^{-1}g)^{-1}t)) = τf(t)`, by left
  invariance of `m`.
- **Chain map.** `δ` is a finite alternating sum of coordinate-deletion maps, and these commute
  with `f ↦ f(g^{-1}·)` pointwise and with the linear functional `m`. So `τδ = δτ`, and
  `‖τ‖ ≤ 1`.
- **Left inverse of restriction.** If `f` is `T`-invariant, then `f(g^{-1}t) = f(t)` for every
  `g`, so `τf = f`.

Hence `τ ∘ res = id` on cochains, and `res : H^*_b(T) → H^*_b(H)` is injective. Restriction is a
ring homomorphism for the cup product, by naturality.

## Step 2. The class `e_b` and its powers

*Lift independence and boundedness.* Replacing a lift `f` by `z^a f` adds `a` to both
`rot(fg)` and `rot(f)`, so `D̄` does not depend on the lifts. `|D̄| ≤ 1` is the standard
defect bound for the translation number.

*`D̄` represents the bounded Euler class.* For each `γ ∈ T`, pick the lift `s(γ)` with
`rot(s(γ)) ∈ [0, 1)`.
- The map `c(γ, η) ∈ Z` defined by `s(γ)s(η) = z^{c(γ,η)} s(γη)` is an integer 2-cocycle.
  It represents the Euler class of `0 → ⟨z⟩ → T̄ → T → 1`, and it is bounded, since
  `c = D̄ − rot∘s(γη) + rot∘s(γ) + rot∘s(η)` is a sum of bounded terms. (Indeed
  `rot(s(γ)s(η)) = c + rot(s(γη))`.)
- With `f := rot ∘ s`, which is bounded, this reads `D̄ = c − δf`.
- So `[D̄_T] = [c]_R =: e_b` in `H²_b(T; R)`, up to a global sign convention. Its image under the
  comparison map is `e_R`.

*All powers are nonzero.*
- `H^*_b(T; R) ≅ R[e_b]` by [FFLM]+[Mo], so `e_b^n ≠ 0`.
- Independently, the comparison map is a ring homomorphism taking `e_b^n` to `e_R^n`, which is
  nonzero by [GS].

By step 1, `(e_b|_H)^n = res(e_b^n) ≠ 0` for every co-amenable `H`. This proves **(A)**.
Restricting the cochain `D̄_T` to `H × H` gives `D̄_H` for the restricted action, so
`e_b|_H = [D̄_H]`.

## Step 3. (B1) and (B2)

**(B1)** is immediate from (A). The cited inputs are:
- amenable groups have `H^{≥1}_b = 0`;
- [FFLM]/[Mo] and the import give bounded acyclicity of `F`. Bounded acyclicity of `F^k` is a
  standard consequence, recorded in [FFLM] and [Mo].

**(B2).** Let `H' ≤ H` have finite index and fix `p ∈ S^1`.
- `H'` is co-amenable in `T`. Given the invariant mean `m` on `T/H`, the mean
  `m'(φ) = m(tH ↦ [H:H']^{-1} Σ_{t'H' ⊂ tH} φ(t'H'))` is `T`-invariant on `T/H'`.
- Fix a lift `p̃` of `p`. For each `γ ∈ H'`, let `ĥ(γ)` be the unique lift fixing `p̃`. Then
  `ĥ` is a homomorphism, because a composite of maps fixing `p̃` fixes `p̃`.
- A lift with a fixed point has `rot = 0`. So, with these lifts, `D̄_{H'} ≡ 0` identically.
- So `e_b|_{H'} = 0`, which contradicts (A) for `H'` with `n = 1`.

## Step 4. (B3)

Let `ρ` be the action of `H` on `S^1`, so `ρ(γ) = γ` as a homeomorphism.

*Reduce to `ρ = σ ∘ ψ`.* Suppose `ρ = θ ∘ (σ∘ψ) ∘ θ^{-1}` for a homeomorphism `θ` of `S^1`.
- If `θ` preserves orientation, choose a lift `θ̃`. Then `rot(θ̃ f θ̃^{-1}) = rot(f)`, so
  `D̄_ρ = D̄_{σψ}`.
- If `θ` reverses orientation, a lift conjugates `z` to `z^{-1}` and negates `rot`. So
  `D̄_ρ = −D̄_{σψ}`.
- In either case, the square of `[D̄_ρ]` equals the square of `[D̄_{σψ}]`.
- `σ(G)` preserves orientation, because `G` is connected.

*Lift `σ`.* Let `Homeo_Z(R)` be the group of lifts, with the compact-open topology.
- `Homeo_Z(R) → Homeo_+(S^1)` is a covering homomorphism with kernel `⟨z⟩`.
- The universal cover `G̃ → G` is simply connected, so `σ` lifts to a continuous
  `σ̃ : G̃ → Homeo_Z(R)` with `σ̃(1) = id`.
- `σ̃` is a homomorphism: `(a, b) ↦ σ̃(ab)` and `(a, b) ↦ σ̃(a)σ̃(b)` lift the same map on the
  connected space `G̃ × G̃` and agree at `(1, 1)`.

*A continuous bounded cocycle on `G`.* Set
`D̄_G(g_1, g_2) = rot(σ̃(ĝ_1)σ̃(ĝ_2)) − rot(σ̃(ĝ_1)) − rot(σ̃(ĝ_2))` for any lifts `ĝ_i ∈ G̃`.
- *Well defined.* Two lifts differ by some `k ∈ ker(G̃ → G)`. Then `σ̃(k)` lifts `id_{S^1}`, so it
  is a translation `z^j`, and the `j`s cancel.
- *Continuous.* `rot` is continuous on `Homeo_Z(R)`, and `G̃ → G` has local continuous sections.
- *Bounded.* `|D̄_G| ≤ 1`.
- *Cocycle.* The pullback of `D̄_G` to `G̃` is `−δ(rot ∘ σ̃)`, so `D̄_G` is a cocycle.

So `κ = [D̄_G] ∈ H²_cb(G; R)`.

*The square dies.* Continuous bounded cochains compute `H^*_cb` (Monod, LNM 1758), compatibly with
cup products.
- By [HO], `D̄_G ∪ D̄_G = δβ` for a continuous bounded 3-cochain `β`.
- Pull back along the homomorphism `ψ : H → G`, which needs no continuity since `H` is discrete.
  Pullback of bounded cochains is a chain map that respects cup products.
- `ψ^*D̄_G = D̄_{σψ}`, because `σ̃(ĝ)` for `ĝ` over `ψ(γ)` is a lift of `σψ(γ)`, and `D̄` does
  not depend on the lift.
- Hence `[D̄_{σψ}]² = [δ ψ^*β] = 0` in `H^4_b(H)`.

So `(e_b|_H)² = 0`. This contradicts (A) with `n = 2`, so `H` is not co-amenable.

*Examples.*
- For `PSL_2(Z) ≤ T`: take `G = PSL_2(R)`, `σ` the projective action on `RP^1 ≅ S^1`, `ψ` the
  inclusion, and `θ` the Minkowski question-mark conjugacy.
- The `PSL_2^{(k)}(R)` actions on `k`-fold covers of the circle are also covered.

## Step 5. (B3') and (B4)

**(B3').** Replace "conjugate" by "semi-conjugate". The bounded Euler class is a
semi-conjugacy invariant [Gh], and it is only recalled here. Step 4 then applies to the class,
since the argument used only `[D̄_ρ]`.

**(B4).** Let `H` be free nonabelian, and write `e_b|_H = [δφ]`.
- Adding a bounded function or a homomorphism to `φ` does not change `[δφ]`.
- If `φ` is `Δ`-decomposable or Brooks, then [AB] gives `[δφ] ∪ [δφ] = 0`.
- This contradicts (A) with `n = 2`.

## Step 6. (C) Forced shape for the open claim

Let `u : H̄ → R` be a homomorphism with `u(z) = 1`, and put `φ̃ = rot − u` on `H̄`.
- *Descends to `H`.* `rot(zf) = rot(f) + 1` and `u(zf) = u(f) + 1`, so `φ̃` is `z`-invariant and
  descends to `φ : H → R`.
- *Homogeneous.* `rot` is homogeneous and `u` is additive, so `φ` is homogeneous.
- *Its coboundary.* For lifts `f, g` of `γ, η`:
  `(δφ)(γ, η) = [rot f + rot g − rot fg] − [u f + u g − u(fg)] = −D̄_H(γ, η)`.
  So `φ` is a quasimorphism, and `[δφ] = −e_b|_H`.

By (A), `[δφ]^n ≠ 0` for every `n` whenever `H` is co-amenable. In particular `δφ` is not a
bounded coboundary, and `φ` is not a homomorphism. `H` must then avoid the cases (B1) to (B4).

*Free case.* `H²(F_r; R) = 0`, so a free `H ≤ T` has `e_R|_H = 0` automatically.
- A free co-amenable subgroup of `T` would therefore witness the open claim.
- By (A), it would also give a class in `H²_b(F_r; R)` with all cup powers nonzero.
- Hofmann (arXiv:2407.17034) records the vanishing of cup products of general degree-two classes
  of free groups as open. So this would resolve that question negatively, and show
  `H^{2n}_b(F_r) ≠ 0` for every `n`. The degree-four case `H^4_b(F_r) ≠ 0` is known
  (Kastenholz, arXiv:2503.22511), but not by cup powers of this kind.

## Step 7. Calibration

Let `T̄` act on the circle through `p : T̄ → T`.
- The pulled-back extension `T̄ ×_T T̄ → T̄` has the diagonal as a homomorphic section, so it
  splits. So `p^* e_Z = 0` and `p^* e_R = 0`.
- `ker p = ⟨z⟩` is amenable, so by [Gr] `p^* : H^*_b(T) → H^*_b(T̄)` is an isomorphism.
  Hence `p^*(e_b)^n ≠ 0` for every `n`.

So vanishing of `e_R` does not force the bounded powers to vanish, for general circle actions.
(A) is a genuine constraint on the open claim, not a refutation of it. ∎
