import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereTopHomology
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Sharp reduction of the missing top-homology family to a suspension tower

The conditional degree API of `Degree.lean` consumes, for each dimension, a chosen
identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` (the type `SphereTopHomologyIso n`).  The genuinely
missing topological input is a term of this type for `n ≥ 1`; it is unprovable
from pinned Mathlib (`v4.28.0`), which has no excision / Mayer–Vietoris / long
exact sequence of a pair / suspension isomorphism for singular homology (see
`Sphere_Top_Homology_Result.md` and `docs/inventories/Sphere_Homology_Inventory.md`).

This file makes the **strongest honest build-clean reduction** of that missing
input, in two complementary directions.

## 1. The `n = 0` obstruction is genuine, not a gap

`SphereTopHomologyIso 0` is `H₀(S⁰; ℤ) ≅ ℤ`, which is **false**: `S⁰` is the
two-point space, so `H₀(S⁰; ℤ) ≅ ℤ²` (one `ℤ` per path component).  We do *not*
fake an `n = 0` identification; instead the structural `SphereOrientation` of
`SphereTopHomology.lean`, whose field is `∀ n, SphereTopHomologyIso n`, is
therefore **uninhabited** (it demands the impossible `n = 0` case).  The honest
replacement is `SphereOrientationPos`, which only asks for identifications in
dimensions `n ≥ 1` — exactly where the integral top-homology degree theory lives.

## 2. The whole `n ≥ 1` family reduces to one suspension theorem

`SphereSuspensionTower` packages exactly the classical inductive input:

* a base identification `H₁(S¹; ℤ) ≅ ℤ`, and
* a **suspension step** `Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)` for every `n ≥ 1`
  (the top-degree restriction of the reduced-homology suspension isomorphism
  `H̃ₖ(ΣX) ≅ H̃ₖ₋₁(X)`).

From a tower, `SphereSuspensionTower.iso` constructs `SphereTopHomologyIso n` for
**all** `n ≥ 1` by a one-line induction, and `SphereSuspensionTower.orientation`
produces a genuine (non-vacuous) `SphereOrientationPos`.  Thus the only remaining
missing Mathlib theorem is the **suspension isomorphism for singular homology of
spheres** (equivalently excision / Mayer–Vietoris); everything else in the
unconditional degree API now follows mechanically.

No fake top-homology isomorphism is constructed here, and every declaration is
build-clean.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## A suspension tower: the single missing topological input -/

/-- A **suspension tower** for the integral top homology of spheres.

It bundles exactly the classical inductive data computing `Hₙ(Sⁿ; ℤ)`:

* `base : H₁(S¹; ℤ) ≅ ℤ`, the degenerate first instance, and
* `step n (h : 1 ≤ n) : Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)`, the top-degree suspension
  isomorphism.

A term of this structure is equivalent to the still-missing suspension theorem for
singular homology; from it the whole family `SphereTopHomologyIso n` (`n ≥ 1`)
follows by induction. -/
structure SphereSuspensionTower where
  /-- The base identification `H₁(S¹; ℤ) ≅ ℤ`. -/
  base : SphereTopHomologyIso 1
  /-- The top-degree suspension isomorphism `Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)`,
  for every `n ≥ 1`. -/
  step : ∀ n : ℕ, 1 ≤ n → (sphereTopHomologyℤ (n + 1) ≅ sphereTopHomologyℤ n)

namespace SphereSuspensionTower

variable (T : SphereSuspensionTower)

/-- The shifted top-homology identification `Hₖ₊₁(Sᵏ⁺¹; ℤ) ≅ ℤ`, defined by
structural recursion on `k`: the base case `k = 0` is `T.base`, and each successor
composes the suspension isomorphism `T.step` with the identification one dimension
lower.  (`Nat.le_induction` only eliminates into `Prop`, so the data-valued family
is built on the shifted index instead.) -/
def isoSucc (k : ℕ) : SphereTopHomologyIso (k + 1) :=
  Nat.rec T.base (fun j ih => (T.step (j + 1) (by omega)) ≪≫ ih) k

/-- From a suspension tower, the top-homology identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` for
every `n ≥ 1`. -/
def iso : ∀ n : ℕ, 1 ≤ n → SphereTopHomologyIso n
  | (k + 1), _ => T.isoSucc k

@[simp]
theorem isoSucc_zero : T.isoSucc 0 = T.base := rfl

end SphereSuspensionTower

/-! ## A non-vacuous positive orientation (dimensions `n ≥ 1`) -/

/-- A **positive sphere orientation**: a choice of top-homology identification
`Hₙ(Sⁿ; ℤ) ≅ ℤ` in every dimension `n ≥ 1`.

Unlike `SphereOrientation` (whose `∀ n` field is uninhabited because it demands the
false `n = 0` case `H₀(S⁰; ℤ) ≅ ℤ`), this structure restricts to the dimensions
`n ≥ 1` where the integral top-homology degree theory lives, and is genuinely
inhabited as soon as a `SphereSuspensionTower` is available. -/
structure SphereOrientationPos where
  /-- The identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` in each dimension `n ≥ 1`. -/
  iso : ∀ n : ℕ, 1 ≤ n → SphereTopHomologyIso n

namespace SphereOrientationPos

variable (o : SphereOrientationPos)

/-- The integer **degree** of a self-map of `Sphere n` (`n ≥ 1`), read off the
supplied top-homology identification `o.iso n hn`.  Honest and unconditional once a
`SphereOrientationPos` is provided. -/
def degree {n : ℕ} (hn : 1 ≤ n) (f : C(Sphere n, Sphere n)) : ℤ :=
  degreeOfIso (o.iso n hn) f

/-- The degree of the identity map is `1`. -/
@[simp]
theorem degree_id {n : ℕ} (hn : 1 ≤ n) :
    o.degree hn (ContinuousMap.id (Sphere n)) = 1 :=
  degreeOfIso_id (o.iso n hn)

/-- The degree is multiplicative: `degree (g ∘ f) = degree g * degree f`. -/
theorem degree_comp {n : ℕ} (hn : 1 ≤ n) (f g : C(Sphere n, Sphere n)) :
    o.degree hn (g.comp f) = o.degree hn g * o.degree hn f :=
  degreeOfIso_comp (o.iso n hn) f g

/-- **Choice independence.** Any two positive orientations assign the same degree. -/
theorem degree_well_defined (o' : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) : o.degree hn f = o'.degree hn f :=
  degreeOfIso_well_defined (o.iso n hn) (o'.iso n hn) f

/-- **Homotopy invariance of the degree** (conditional on the prism operator).
Homotopic self-maps of `Sphere n` (`n ≥ 1`) have equal degree. -/
theorem degree_eq_of_homotopic (prism : SingularPrismOperator) {n : ℕ} (hn : 1 ≤ n)
    {f g : C(Sphere n, Sphere n)} (h : ContinuousMap.Homotopic f g) :
    o.degree hn f = o.degree hn g :=
  degreeOfIso_eq_of_homotopic prism (o.iso n hn) h

end SphereOrientationPos

/-- A suspension tower yields a genuine (non-vacuous) positive orientation. -/
def SphereSuspensionTower.orientation (T : SphereSuspensionTower) :
    SphereOrientationPos :=
  ⟨T.iso⟩

@[simp]
theorem SphereSuspensionTower.orientation_iso (T : SphereSuspensionTower)
    (n : ℕ) (hn : 1 ≤ n) : T.orientation.iso n hn = T.iso n hn := rfl

/-! ## The `n = 0` obstruction, proved

The `n = 0` case is genuinely *not* a missing input but a true obstruction:
`H₀(S⁰; ℤ) ≅ ℤ²`, so there is no identification `H₀(S⁰; ℤ) ≅ ℤ`.  Consequently the
structural `SphereOrientation` of `SphereTopHomology.lean` (whose field demands a
term of `SphereTopHomologyIso n` for *every* `n`, including `n = 0`) is
**uninhabited** — which is exactly why the non-vacuous `SphereOrientationPos`
(restricted to `n ≥ 1`) is the correct structure. -/

open Limits

/-- `H₀(S⁰; ℤ)` is the categorical coproduct of one copy of `ℤ` per point of the
two-point space `S⁰`, via Mathlib's totally-disconnected computation. -/
noncomputable def sphere0_H0_iso_coprod :
    sphereTopHomologyℤ 0 ≅ ∐ (fun _ : (TopCat.sphere.{0} 0 : Type) ↦ ModuleCat.of ℤ ℤ) :=
  singularHomologyFunctorZeroOfTotallyDisconnectedSpace
    (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) (TopCat.sphere.{0} 0)

/-
The two-point space `S⁰` has exactly two points.
-/
theorem card_topCatSphere_zero :
    Nat.card (TopCat.sphere.{0} 0 : Type) = 2 := by
  -- The sphere of dimension 0 is just two points, so its cardinality is 2.
  have h_card : Nat.card (Sphere 0) = 2 := by
    rw [ Nat.card_eq_two_iff ];
    refine' ⟨ ⟨ EuclideanSpace.single 0 1, _ ⟩, ⟨ -EuclideanSpace.single 0 1, _ ⟩, _, _ ⟩ <;> norm_num [ Set.ext_iff ];
    · exact ne_of_apply_ne ( fun x => x 0 ) ( by norm_num );
    · intro a ha; rw [ EuclideanSpace.norm_eq ] at ha; simp_all +decide [ Fin.eq_zero ] ;
      exact Or.imp ( fun h => by ext i; fin_cases i; aesop ) ( fun h => by ext i; fin_cases i; aesop ) ha;
  convert h_card using 1;
  fapply Nat.card_congr;
  exact ( topCatSphereHomeomorph 0 ).toEquiv

/-
The `ℤ`-rank of `H₀(S⁰; ℤ)` is `2`: through Mathlib's totally-disconnected
computation and `ModuleCat.coprodIsoDirectSum`, it is `ℤ`-linearly isomorphic to
`⨁_{x ∈ S⁰} ℤ`, a free `ℤ`-module of rank `Nat.card S⁰ = 2`.
-/
theorem finrank_sphereTopHomologyℤ_zero :
    Module.finrank ℤ (sphereTopHomologyℤ 0) = 2 := by
  classical
  have hFin : Finite (TopCat.sphere.{0} 0 : Type) :=
    Finite.of_injective _ (topCatSphereHomeomorph 0).injective
  letI : Fintype (TopCat.sphere.{0} 0 : Type) := Fintype.ofFinite _
  -- `H₀(S⁰; ℤ)` is `ℤ`-linearly isomorphic to `⨁_{x ∈ S⁰} ℤ`.
  have e := (sphere0_H0_iso_coprod ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : (TopCat.sphere.{0} 0 : Type) ↦
        ModuleCat.of ℤ ℤ)).toLinearEquiv
  rw [e.finrank_eq, Module.finrank_directSum]
  simp only [Module.finrank_self, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, card_topCatSphere_zero]

/-- **The `n = 0` obstruction is genuine.** There is no identification
`H₀(S⁰; ℤ) ≅ ℤ`: `H₀(S⁰; ℤ)` has `ℤ`-rank `2` (`finrank_sphereTopHomologyℤ_zero`),
whereas `ℤ` has rank `1`. -/
theorem sphereTopHomologyIso_zero_isEmpty : IsEmpty (SphereTopHomologyIso 0) := by
  rw [isEmpty_iff]
  intro e
  have h1 : Module.finrank ℤ (sphereTopHomologyℤ 0) = Module.finrank ℤ (ModuleCat.of ℤ ℤ) :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  rw [finrank_sphereTopHomologyℤ_zero] at h1
  simp [Module.finrank_self] at h1

/-- The structural `SphereOrientation` is uninhabited, because it demands the
impossible `n = 0` identification `H₀(S⁰; ℤ) ≅ ℤ`.  (The correct non-vacuous
structure is `SphereOrientationPos`, which only requires `n ≥ 1`.) -/
theorem sphereOrientation_isEmpty : IsEmpty SphereOrientation := by
  refine ⟨fun o => ?_⟩
  exact sphereTopHomologyIso_zero_isEmpty.false (o.iso 0)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
