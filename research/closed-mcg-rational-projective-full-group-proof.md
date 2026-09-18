---
rg: 2
id: closed-mcg-rational-projective-full-group-proof
kind: route
title: Proof that the closed-surface mapping class group embeds in the full clopen-transitive group of integral projective germs on the rational Cantorization
target: closed-mcg-embeds-in-rational-projective-full-group
---

Notation as in `closed-mcg-embeds-in-rational-projective-full-group`. Elementary,
except for the trust surface listed there.

## 1. `Ŝ_m` is a Cantor space

- `B_m` is countable, since there are countably many integral forms.
- `B_m` is atomless: every nonempty rational polyhedral regular open set contains
  two disjoint nonempty ones, cut out by a rational hyperplane through an
  interior point.
- A countable atomless Boolean algebra has a Cantor Stone space.
- Each ultrafilter `ξ` converges to a unique point `π(ξ) ∈ S^m`, because rational
  polyhedral sets of arbitrarily small diameter separate points. So
  `π : Ŝ_m → S^m` is continuous, surjective and `Γ_m`-equivariant.
- `g ∈ Γ_m` maps `H_ℓ` to `H_{ℓ∘g^{-1}}`, so it preserves `B_m` and acts on
  `Ŝ_m`.

## 2. Topological freeness

- Suppose `g` fixes a nonempty clopen `U` pointwise, with `U` corresponding to
  `u ∈ B_m`.
- Then `g` fixes every `v ≤ u` in `B_m`.
- So `g` fixes every point of the open set `u ⊂ S^m`, since each such point is
  the intersection of the closures of the small `v ≤ u` containing it.
- Then `g` acts as the identity on an open cone of `R^{m+1}`, so `g = λI` with
  `λ > 0`, and `g = I`.
- Hence the action is topologically free. Two group elements with the same germ
  at a point agree on a neighbourhood, so they are equal. So the germ groupoid is
  the transformation groupoid `Γ_m ⋉ Ŝ_m`, which is Hausdorff and effective.

## 3. Unimodular decomposition

- Let `u ∈ B_m` be nonempty. Its closure is a finite union of rational
  polyhedral cones, which can be triangulated into rational simplicial cones.
- Every rational fan has a unimodular refinement (toric resolution, any
  dimension). Take one.
- Each maximal cone is `cone(w_0, …, w_m)` with `(w_i)` a `Z`-basis, so its
  interior is `gΔ` with `g ∈ Γ_m` sending `e_i ↦ w_i`.
- Distinct maximal cones have disjoint interiors, and the union of their closures
  is `cl u`. So in `B_m`, `u` is the disjoint join of the `gΔ`, and `U` is a
  finite disjoint union of the clopens `gΔ`.
- **Splitting `Δ`.** The stellar subdivision of `cone(e_0, …, e_m)` at `e_0 + e_1`
  gives `cone(e_0+e_1, e_1, e_2, …, e_m)` and `cone(e_0, e_0+e_1, e_2, …, e_m)`.
  Both are unimodular, with determinant `±1`. So `Δ = g'Δ ⊔ g''Δ`.

## 4. Minimality and clopen transitivity

- **Minimality.** Let `U` be a nonempty clopen. By §3, `U ⊇ gΔ` for some `g`.
  The `2^{m+1}` sign changes `ε ∈ Γ_m` give orthants `εΔ`, whose union is dense
  in `S^m`. So `⋁ εΔ` is the top element and `⋃_ε ε g^{-1} U = Ŝ_m`. Finitely
  many translates of every nonempty clopen cover, so every orbit is dense.
- **`Δ ≅ kΔ`.** Iterating `Δ = g'Δ ⊔ g''Δ` gives, for every `k ≥ 1`, a local map
  from `Δ` onto a disjoint union of `k` translates of `Δ`.
- **Clopen transitivity.** By §3, every nonempty clopen `U` is a disjoint union of
  `k_U` translates of `Δ`, so `U ≅ k_U Δ ≅ Δ` by local maps. Hence any two
  nonempty clopens are joined by a local map.
- **Fullness.** `𝒯_m` is a topological full group by definition.
- **Containment.** `Γ_m ≤ 𝒯_m`, taking the trivial partition.

## 5. The mapping class group

Let `g ≥ 2` and `n = 6g − 6`. Recalled standard facts:
- `ML(S_g)` has an atlas of finitely many complete train-track charts. Each is a
  rational polyhedral cone in the weight space of a track `τ`.
- Identify the span of each chart with `R^n` by a `Z`-basis of its lattice of
  integral weights.
- The integral points in every chart are exactly the integral multicurves. So the
  chart transitions, and the action of every `f ∈ Mod(S_g)` (which sends chart
  `τ` to chart `fτ` by the identity on weights), are piecewise `GL_n(Z)` with
  finitely many rational polyhedral pieces.

Let `B(PML)` be the Boolean algebra of regular open sets that are rational
polyhedral in every chart, and `Ŝ(PML)` its Stone space.
- The notion is chart-independent, because the transitions are PIL.
- `f` maps `B(PML)` to itself, since a PIL map with rational pieces sends
  rational polyhedral sets to finite unions of such.
- So `f` induces a homeomorphism `f̂` of `Ŝ(PML)`, and `f ↦ f̂` is a
  homomorphism by Stone duality.
- On each piece of a finite clopen partition, `f̂` is given in charts by an
  element of `GL_n(Z)`. So `f̂` lies in the full group of the integral projective
  germ groupoid `𝒢_{PML}`.

**Identification with `𝒯_m`, `m = n − 1`.**
- By §3 applied chartwise, `Ŝ(PML)` is a finite disjoint union of chart images of
  unimodular simplices, each identified with `Δ ⊂ Ŝ_m` by a chart map composed
  with an element of `GL_n(Z)`.
- Local maps between pieces are, in these coordinates, piecewise `GL_n(Z)`.
- So `𝒢_{PML} ≅ (Γ_m ⋉ Ŝ_m)|_{W}` for a clopen `W ⊂ Ŝ_m` that is a disjoint union
  of `k` translates of `Δ`.
- By §4, `W ≅ Ŝ_m` through a local homeomorphism `h`, and conjugation by `h`
  gives `[[𝒢_{PML}]] ≅ [[Γ_m ⋉ Ŝ_m]] = 𝒯_m`.

**Faithfulness.**
- The projection `Ŝ(PML) → PML` is surjective and equivariant.
- So `f̂ = 1` forces `f` to act trivially on `PML`.
- For `g ≥ 3` that forces `f = 1`. For `g = 2` the kernel is the hyperelliptic
  involution, which no torsion-free subgroup contains.

## 6. Calibration, `m = 1`

- `Ŝ_1` is `S^1` with every rational ray doubled.
- The four quadrants `εΔ` are unimodular cones, and each subdivides by mediants
  `cone(v,w) = cone(v, v+w) ⊔ cone(v+w, w)`. This gives four binary trees whose
  boundaries tile `Ŝ_1`.
- A prefix replacement between tree nodes `cone(v,w) → cone(v',w')` is the
  restriction of the `g ∈ GL_2(Z)` with `v ↦ v'`, `w ↦ w'`. That `g` maps mediant
  subtrees onto mediant subtrees.
- So `V ≅ V_{2,4}` acts inside `𝒯_1`.
- `SL_2(Z) ≤ 𝒯_1` directly, which is the Farey/Serret picture of
  `train-track-trace-groupoid-hosts-closed-mcg`.
