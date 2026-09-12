import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Degree
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnLowDimensional

/-!
# Top singular homology of spheres: abbreviations, model bridge, low-dim cases

This file assembles the **genuine, build-clean** support layer toward the missing
topological input

```text
Hₙ(Sⁿ; ℤ) ≅ ℤ
```

that would turn the conditional degree API of `Degree.lean` into an unconditional
topological degree.  The full computation `Hₙ(Sⁿ; ℤ) ≅ ℤ` is **not** provable from
the pinned Mathlib (it needs excision / Mayer–Vietoris / the long exact sequence of
a topological pair / a suspension isomorphism, none of which exist in
`Mathlib v4.28.0`; see `docs/inventories/Sphere_Homology_Inventory.md`).  Per the
project policy this file therefore implements the **largest build-clean useful
subset** and contains **no fake top-homology isomorphism**:

* **Top-homology abbreviations.** `sphereHomologyℤ k n = Hₖ(Sⁿ; ℤ)` over the
  categorical sphere `TopCat.sphere n`, and `sphereTopHomologyℤ n = Hₙ(Sⁿ; ℤ)`.
* **Model bridge.** `sphereModelHomologyIso k n` transports `Hₖ(TopCat.sphere n)`
  to `Hₖ` of the project's raw subtype model `Sphere n`, by functoriality of
  `singularHomologyℤ` applied to the bridge iso `topCatSphereIso`.
* **Genuine low-dimensional case `n = 0`.** `Sphere 0` is the two-point set
  `{±e}`, hence finite, discrete and totally disconnected; via the bridge so is
  `TopCat.sphere 0`.  Mathlib's
  `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` then gives the
  honest vanishing `Hₖ(S⁰; ℤ) = 0` for `k ≠ 0`
  (`sphere0_singularHomologyℤ_isZero`).  Note that the *top* `n = 0` case is
  genuinely **not** `≅ ℤ`: `H₀(S⁰; ℤ) ≅ ℤ²` (two path components), so the degree
  theory is meaningful only for `n ≥ 1`; no `SphereTopHomologyIso 0` is asserted.
* **Conditional isomorphism wrappers.** `SphereTopHomologyIso n` is the *type* of
  identifications `Hₙ(Sⁿ; ℤ) ≅ ℤ` (over `TopCat.sphere n`).  It transports across
  the model bridge (`sphereTopHomologyIso_of_modelIso` and its inverse), so the
  computation may be carried out in whichever sphere model is convenient.
* **Bundled orientation ⇒ unconditional degree.** `SphereOrientation` bundles a
  family `∀ n, SphereTopHomologyIso n` (exactly the missing input).  Given one,
  `SphereOrientation.degree` is an honest integer degree with `degree_id`,
  `degree_comp`, choice-independence (`degree_well_defined`) and, assuming the
  prism operator, homotopy invariance (`degree_eq_of_homotopic`).  This is a
  *parameterised* wrapper, **not** a fake global `degree`: no `SphereOrientation`
  is constructed here.

## Exact remaining blocker

The single missing piece is a term of `SphereTopHomologyIso n` for `n ≥ 1` (i.e.
`Hₙ(Sⁿ; ℤ) ≅ ℤ`).  Its dependency DAG in pinned Mathlib:

```text
Hₙ(Sⁿ;ℤ) ≅ ℤ
  ⇐ reduced suspension iso  H̃ₖ(Sⁿ) ≅ H̃ₖ₋₁(Sⁿ⁻¹)            [ABSENT]
      ⇐ excision / Mayer–Vietoris for singular homology       [ABSENT]
      ⇐ LES of the topological pair (𝔻ⁿ, Sⁿ⁻¹)               [ABSENT: no
            relative singular homology of a pair of spaces]
      ⇐ contractibility ⇒ Hₖ(𝔻ⁿ)=0 (k>0)                      [needs the prism
            operator `SingularPrismOperator`, link 8b]
  base case  S⁰:  Hₖ(S⁰)=0 (k≠0) DONE here; H₀(S⁰)≅ℤ²         [the k=0 part is
            not packaged]
```

Everything above the base case is the genuinely missing topological theory.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## Top-homology abbreviations over `TopCat.sphere n` -/

/-- `Hₖ(Sⁿ; ℤ)`: the `k`-th integral singular homology of Mathlib's categorical
sphere object `TopCat.sphere n`. -/
noncomputable abbrev sphereHomologyℤ (k n : ℕ) : ModuleCat.{0} ℤ :=
  (singularHomologyℤ k).obj (TopCat.sphere.{0} n)

/-- The **top** homology `Hₙ(Sⁿ; ℤ)` — the group that should be `≅ ℤ` and that the
topological degree reads. -/
noncomputable abbrev sphereTopHomologyℤ (n : ℕ) : ModuleCat.{0} ℤ :=
  sphereHomologyℤ n n

/-! ## Model bridge: `TopCat.sphere n` vs. the raw `Sphere n` model -/

/-- **Model bridge on homology.** The integral singular homology of the
categorical sphere `TopCat.sphere n` is isomorphic to that of the project's raw
subtype model `Sphere n`, by applying the homology functor to the bridge
isomorphism `topCatSphereIso` (`TopCatBridge.lean`). -/
noncomputable def sphereModelHomologyIso (k n : ℕ) :
    sphereHomologyℤ k n ≅ (singularHomologyℤ k).obj (TopCat.of (Sphere n)) :=
  (singularHomologyℤ k).mapIso (topCatSphereIso n)

/-! ## Genuine low-dimensional case: `n = 0`

`Sphere 0` is the unit sphere in `ℝ¹`, i.e. the two-point set `{±e}`. It is finite
(at most two points by `sphere_zero_eq_or_neg`), hence discrete and totally
disconnected; the bridge homeomorphism transports this to `TopCat.sphere 0`. -/

/-- `Sphere 0` is finite: every point equals a fixed `p` or its antipode `-p`
(`sphere_zero_eq_or_neg`), so it is the image of `Bool`. -/
instance instFiniteSphereZero : Finite (Sphere 0) := by
  have p : Sphere 0 := ⟨EuclideanSpace.single 0 1, by norm_num [EuclideanSpace.norm_eq]⟩
  apply Finite.of_surjective (fun b : Bool => if b then p else -p)
  intro y
  rcases sphere_zero_eq_or_neg y p with h | h
  · exact ⟨true, by simp [h]⟩
  · exact ⟨false, by simp [h]⟩

/-- `TopCat.sphere 0` is totally disconnected: it is homeomorphic (via
`topCatSphereHomeomorph`) to the finite, hence discrete, two-point set
`Sphere 0`. -/
instance instTotallyDisconnectedTopCatSphereZero :
    TotallyDisconnectedSpace (TopCat.sphere.{0} 0 : Type) :=
  (topCatSphereHomeomorph 0).symm.totallyDisconnectedSpace

/-- **Genuine low-dimensional homology of `S⁰`.** For `k ≠ 0`,
`Hₖ(S⁰; ℤ) = 0`, since `S⁰` is totally disconnected.  (The `k = 0` value is
`H₀(S⁰; ℤ) ≅ ℤ²`, which is *not* `ℤ`; the degree theory therefore concerns
`n ≥ 1`.) -/
theorem sphere0_singularHomologyℤ_isZero (k : ℕ) (hk : k ≠ 0) :
    Limits.IsZero (sphereHomologyℤ k 0) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) k (ModuleCat.of ℤ ℤ) (TopCat.sphere.{0} 0) hk

/-! ## Conditional isomorphism wrappers -/

/-- The **type of top-homology identifications** `Hₙ(Sⁿ; ℤ) ≅ ℤ` (over
`TopCat.sphere n`).  A term of this type for `n ≥ 1` is exactly the missing
topological input; none is constructed in this file. -/
abbrev SphereTopHomologyIso (n : ℕ) : Type :=
  sphereTopHomologyℤ n ≅ ModuleCat.of ℤ ℤ

/-- Transport an identification `Hₙ(Sⁿ) ≅ ℤ` from the raw `Sphere n` model to the
categorical `TopCat.sphere n` model, through the homology model bridge. -/
def sphereTopHomologyIso_of_modelIso {n : ℕ}
    (e : (singularHomologyℤ n).obj (TopCat.of (Sphere n)) ≅ ModuleCat.of ℤ ℤ) :
    SphereTopHomologyIso n :=
  (sphereModelHomologyIso n n).trans e

/-- Transport an identification `Hₙ(Sⁿ) ≅ ℤ` from the categorical
`TopCat.sphere n` model to the raw `Sphere n` model, through the homology model
bridge. -/
def modelIso_of_sphereTopHomologyIso {n : ℕ} (e : SphereTopHomologyIso n) :
    (singularHomologyℤ n).obj (TopCat.of (Sphere n)) ≅ ModuleCat.of ℤ ℤ :=
  (sphereModelHomologyIso n n).symm.trans e

/-! ## Bundled orientation ⇒ unconditional degree

`SphereOrientation` bundles the missing input — a choice of `Hₙ(Sⁿ; ℤ) ≅ ℤ` in
every dimension — and packages the conditional degree of `Degree.lean` as an
*unconditional* degree relative to that data.  No `SphereOrientation` is built
here; it is a hypothesis for any downstream consumer. -/

/-- A choice of top-homology identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` in every dimension.
This bundles exactly the missing topological input; constructing one is equivalent
to proving `Hₙ(Sⁿ; ℤ) ≅ ℤ` for all `n`. -/
structure SphereOrientation where
  /-- The identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` in dimension `n`. -/
  iso : ∀ n, SphereTopHomologyIso n

namespace SphereOrientation

variable (o : SphereOrientation)

/-- The integer **degree** of a self-map of `Sphere n`, read off the supplied
top-homology identification `o.iso n`.  Honest and unconditional once a
`SphereOrientation` is provided. -/
def degree {n : ℕ} (f : C(Sphere n, Sphere n)) : ℤ :=
  degreeOfIso (o.iso n) f

/-- The degree of the identity map is `1`. -/
@[simp]
theorem degree_id (n : ℕ) : o.degree (ContinuousMap.id (Sphere n)) = 1 :=
  degreeOfIso_id (o.iso n)

/-- The degree is multiplicative: `degree (g ∘ f) = degree g * degree f`. -/
theorem degree_comp {n : ℕ} (f g : C(Sphere n, Sphere n)) :
    o.degree (g.comp f) = o.degree g * o.degree f :=
  degreeOfIso_comp (o.iso n) f g

/-- **Choice independence.** Any two orientations assign the same degree, since the
relative degree is independent of the chosen identification. -/
theorem degree_well_defined (o' : SphereOrientation) {n : ℕ}
    (f : C(Sphere n, Sphere n)) : o.degree f = o'.degree f :=
  degreeOfIso_well_defined (o.iso n) (o'.iso n) f

/-- **Homotopy invariance of the degree** (conditional on the prism operator).
Homotopic self-maps of `Sphere n` have equal degree. -/
theorem degree_eq_of_homotopic (prism : SingularPrismOperator) {n : ℕ}
    {f g : C(Sphere n, Sphere n)} (h : ContinuousMap.Homotopic f g) :
    o.degree f = o.degree g :=
  degreeOfIso_eq_of_homotopic prism (o.iso n) h

end SphereOrientation

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
