import GroupApproximation.CharClass.CohomologyDeltaLift

/-!
# The class of a cocycle, for an arbitrary `F₂` cochain complex

`cocycleClass` of the vendored development is tied to the singular cochain complex
of a space.  The Mayer–Vietoris short exact sequence has terms that are **not**
cochain complexes of spaces — they are duals of subordinate-chain complexes and of
the small-chain complex — so computing with the connecting map needs the same
notion for an arbitrary cochain complex over `F₂`, together with its naturality.

`clsOf K n z hz` is that class; it agrees with `cocycleClass` on the nose for the
singular cochain complex, it is surjective, and a cochain map sends the class of a
cocycle to the class of its image.  Those three facts are what turn the abstract
description of `δ` in `CohomologyDeltaLift.lean` into a statement about cochains.

## Main declarations

* `CohClass.clsOf`, `CohClass.clsOf_eq_cocycleClass`.
* `CohClass.clsOf_surjective`.
* `CohClass.homologyMap_clsOf` — naturality.
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace CohClass

variable {K L : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ}

/-- The class in `H^n(K)` of a cocycle of `K`. -/
def clsOf (K : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (n : ℕ) (z : K.X n)
    (hz : (K.d n (n + 1)).hom z = 0) : K.homology n :=
  (K.homologyπ n).hom (K.cyclesMk z (n + 1) (ComplexShape.next_eq' _ (upRel n)) hz)

/-- For the singular cochain complex of a space this is the vendored
`cocycleClass`. -/
theorem clsOf_eq_cocycleClass (X : TopCat.{0}) (n : ℕ)
    (z : singularCochainGroup (ZMod 2) X n)
    (hz : cochainCoboundary (ZMod 2) X n z = 0) :
    clsOf (cochainCxZMod2 X) n z hz = cocycleClass X n z hz := rfl

/-- The image of a cycle under `iCycles` is a cocycle. -/
theorem d_iCycles (K : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (n : ℕ)
    (c : K.cycles n) : (K.d n (n + 1)).hom ((K.iCycles n).hom c) = 0 := by
  have h := K.iCycles_d n (n + 1)
  change ((K.iCycles n ≫ K.d n (n + 1)).hom c) = 0
  rw [h]
  rfl

/-- **Every class is the class of a cocycle.** -/
theorem clsOf_surjective (K : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (n : ℕ)
    (a : K.homology n) :
    ∃ (z : K.X n) (hz : (K.d n (n + 1)).hom z = 0), clsOf K n z hz = a := by
  have hepi : Function.Surjective ((K.homologyπ n).hom) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨c, hc⟩ := hepi a
  refine ⟨(K.iCycles n).hom c, d_iCycles K n c, ?_⟩
  rw [clsOf, ← hc]
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance
  exact K.i_cyclesMk _ _ _ _

/-- **Naturality of the class of a cocycle.**  A map of cochain complexes sends the
class of a cocycle to the class of its image. -/
theorem homologyMap_clsOf (φ : K ⟶ L) (n : ℕ) (z : K.X n)
    (hz : (K.d n (n + 1)).hom z = 0)
    (hz' : (L.d n (n + 1)).hom ((φ.f n).hom z) = 0) :
    (HomologicalComplex.homologyMap φ n).hom (clsOf K n z hz)
      = clsOf L n ((φ.f n).hom z) hz' := by
  rw [clsOf, ← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality,
    ModuleCat.comp_apply, clsOf]
  apply congrArg (L.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).1 inferInstance
  calc
    _ = ((K.iCycles n ≫ φ.f n).hom)
          (K.cyclesMk z (n + 1) (ComplexShape.next_eq' _ (upRel n)) hz) :=
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ n) _
    _ = (φ.f n).hom z := by
      rw [ModuleCat.comp_apply]
      exact congrArg (φ.f n).hom (K.i_cyclesMk _ _ _ _)
    _ = _ := (L.i_cyclesMk _ _ _ _).symm

/-- A cochain map preserves cocycles. -/
theorem d_map_eq_zero (φ : K ⟶ L) (n : ℕ) (z : K.X n)
    (hz : (K.d n (n + 1)).hom z = 0) :
    (L.d n (n + 1)).hom ((φ.f n).hom z) = 0 := by
  have hcomm := φ.comm n (n + 1)
  rw [← ModuleCat.comp_apply, hcomm, ModuleCat.comp_apply, hz, map_zero]

end CohClass

end

end GroupApproximation.CharClass
