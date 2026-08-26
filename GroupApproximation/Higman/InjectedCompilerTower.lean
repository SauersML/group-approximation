import GroupApproximation.Higman.ExplicitFreeEdge

/-!
# An injected free-edge compiler tower

This file composes the honest HNN extensions from `ExplicitFreeEdge`.
There is no appeal to an embedding theorem: Mathlib's Britton normal form
gives injectivity of the base map at each individual HNN edge, and ordinary
composition gives injectivity through the whole tower.

The intended order is

* a `tau` shear edge;
* the `d` edge;
* the `sigma` edge;
* the corrected conjugated centralizer detector, attached last.

The first three edges are stored as `ExplicitFreeEdge.Data`.  Consequently
their only non-formal obligations are the two visibly displayed free-group
evaluation maps and proofs that those maps are injective.  The constructors
`evaluatedShearData`, `dData`, and `sigmaData` expose those obligations.
-/

namespace GroupApproximation
namespace Higman
namespace InjectedCompilerTower

open HNNExtension
open ExplicitFreeEdge

universe u v w z

variable {G : Type u} [Group G]

/-! ## A shear transported through a free evaluation map -/

/-- The Nielsen shear remains injective before it is evaluated in a base
group. -/
theorem shearForward_injective {X : Type v} (payload : FreeGroup X) :
    Function.Injective (shearForward payload) := by
  intro a b hab
  have h := congrArg (shearBackward payload) hab
  simpa only [← MonoidHom.comp_apply,
    shearBackward_comp_shearForward, MonoidHom.id_apply] using h

/-- Evaluate both sides of the Nielsen shear in an arbitrary group.  The
target is injective for formal reasons once the displayed source evaluation
is injective. -/
def evaluatedShearData {X : Type v}
    (eval : FreeGroup (X ⊕ Unit) →* G) (heval : Function.Injective eval)
    (payload : FreeGroup X) : Data (X ⊕ Unit) G where
  source := eval
  target := eval.comp (shearForward payload)
  source_injective := heval
  target_injective := heval.comp (shearForward_injective payload)

@[simp] theorem evaluatedShearData_source {X : Type v}
    (eval : FreeGroup (X ⊕ Unit) →* G) (heval : Function.Injective eval)
    (payload : FreeGroup X) :
    (evaluatedShearData eval heval payload).source = eval := rfl

@[simp] theorem evaluatedShearData_target {X : Type v}
    (eval : FreeGroup (X ⊕ Unit) →* G) (heval : Function.Injective eval)
    (payload : FreeGroup X) :
    (evaluatedShearData eval heval payload).target =
      eval.comp (shearForward payload) := rfl

/-! ## Three composable HNN edges -/

/-- The exact algebraic data of the three inner compiler layers.  Every
field is a concrete `ExplicitFreeEdge.Data`, hence records two homomorphisms
from a displayed free group and injectivity proofs for precisely those maps.
-/
structure ThreeStage (G : Type u) [Group G] where
  TauIndex : Type v
  tau : Data TauIndex G
  DIndex : Type w
  d : Data DIndex (Extension tau)
  SigmaIndex : Type z
  sigma : Data SigmaIndex (Extension d)

variable (T : ThreeStage G)

/-- The group after the `tau` edge. -/
abbrev Tau : Type (max u v) := Extension T.tau

/-- The group after the `d` edge. -/
abbrev D : Type (max u v w) := Extension T.d

/-- The group after the `sigma` edge. -/
abbrev Top : Type (max u v w z) := Extension T.sigma

/-- The literal base inclusion at the `tau` edge. -/
def baseToTau : G →* Tau T := of

/-- The literal base inclusion at the `d` edge. -/
def tauToD : Tau T →* D T := of

/-- The literal base inclusion at the `sigma` edge. -/
def dToTop : D T →* Top T := of

/-- The original base mapped through all three inner layers. -/
def baseToTop : G →* Top T :=
  (dToTop T).comp ((tauToD T).comp (baseToTau T))

/-- Britton injectivity at the `tau` edge. -/
theorem baseToTau_injective : Function.Injective (baseToTau T) :=
  HNNExtension.of_injective (φ := edgeEquiv T.tau)

/-- Britton injectivity at the `d` edge. -/
theorem tauToD_injective : Function.Injective (tauToD T) :=
  HNNExtension.of_injective (φ := edgeEquiv T.d)

/-- Britton injectivity at the `sigma` edge. -/
theorem dToTop_injective : Function.Injective (dToTop T) :=
  HNNExtension.of_injective (φ := edgeEquiv T.sigma)

/-- The starting group embeds in the completed three-layer tower. -/
theorem baseToTop_injective : Function.Injective (baseToTop T) :=
  (dToTop_injective T).comp ((tauToD_injective T).comp (baseToTau_injective T))

/-! ## The corrected detector, attached after the tower -/

variable {F K : Type u} [Group F] [Group K]

/-- A three-stage compiler whose starting group is `K * ⟨q⟩`, realized as
the HNN extension of `K` over the trivial subgroup. -/
abbrev FreeLetterTower := ThreeStage (ConjugatedDetector.FreeLetterExtension K)

/-- The final central HNN detector, attached only after `tau`, `d`, and
`sigma` have been completed. -/
abbrev Outermost (L : Subgroup K) (T : FreeLetterTower (K := K)) : Type _ :=
  ConjugatedDetector.FreeOutermostExtension L (baseToTop T)

/-- The completed inner tower embeds in the outermost detector. -/
def topToOutermost (L : Subgroup K) (T : FreeLetterTower (K := K)) :
    Top T →* Outermost L T := of

/-- The free-letter base mapped through all four layers. -/
def freeLetterToOutermost (L : Subgroup K)
    (T : FreeLetterTower (K := K)) :
    ConjugatedDetector.FreeLetterExtension K →* Outermost L T :=
  (topToOutermost L T).comp (baseToTop T)

/-- The original benign-witness ambient group mapped through the free-letter
step, all three compiler layers, and the final detector. -/
def originalToOutermost (L : Subgroup K)
    (T : FreeLetterTower (K := K)) : K →* Outermost L T :=
  (freeLetterToOutermost L T).comp
    (of : K →* ConjugatedDetector.FreeLetterExtension K)

/-- Britton injectivity for the final, central detector edge. -/
theorem topToOutermost_injective (L : Subgroup K)
    (T : FreeLetterTower (K := K)) :
    Function.Injective (topToOutermost L T) :=
  of_injective_centHNN _

/-- The free-letter base survives the complete four-edge construction. -/
theorem freeLetterToOutermost_injective (L : Subgroup K)
    (T : FreeLetterTower (K := K)) :
    Function.Injective (freeLetterToOutermost L T) :=
  (topToOutermost_injective L T).comp (baseToTop_injective T)

/-- In particular the original benign-witness ambient group survives the
complete tower. -/
theorem originalToOutermost_injective (L : Subgroup K)
    (T : FreeLetterTower (K := K)) :
    Function.Injective (originalToOutermost L T) :=
  (freeLetterToOutermost_injective L T).comp
    (of_injective_centHNN (⊥ : Subgroup K))

/-- The corrected edge subgroup remains disjoint from the old embedded copy
of `F` at the top of the three inner layers. -/
theorem detectorEdge_inf_embedded_atTop
    (L : Subgroup K) (e : F →* K) (T : FreeLetterTower (K := K)) :
    (ConjugatedDetector.freeLetterConjugateSubgroup L).map (baseToTop T) ⊓
        (ConjugatedDetector.freeLetterEmbeddedSubgroup e).map (baseToTop T) = ⊥ :=
  ConjugatedDetector.tower_freeLetterConjugate_inf_embedded
    L e (baseToTop T) (baseToTop_injective T)

/-- The literal payload tested by the outermost stable letter. -/
def detectedWord (L : Subgroup K) (e : F →* K)
    (T : FreeLetterTower (K := K)) (f : F) : Outermost L T :=
  ConjugatedDetector.freeDetectedWord L e (baseToTop T) f

/-- **End-to-end detector survival.**

Start with a subgroup cut `L.comap e = N`, adjoin the free conjugating letter,
pass through the explicit `tau`, `d`, and `sigma` HNN edges, and only then
adjoin the detector.  Every intervening base map is injective by Britton's
lemma.  Therefore the final stable letter commutes with the transported word
exactly for the elements of `N`.

No compiler theorem or literature result occurs among the assumptions.  To
instantiate the inner tower, the remaining obligations are exactly the
`source_injective` and `target_injective` fields of its three displayed
`ExplicitFreeEdge.Data` values. -/
theorem commute_outerStable_detectedWord_iff
    (N : Subgroup F) (L : Subgroup K) (e : F →* K)
    (T : FreeLetterTower (K := K)) (hcut : L.comap e = N) (f : F) :
    Commute (t : Outermost L T) (detectedWord L e T f) ↔ f ∈ N := by
  exact ConjugatedDetector.commute_freeStable_freeDetectedWord_iff
    N L e (baseToTop T) (baseToTop_injective T) hcut f

end InjectedCompilerTower
end Higman
end GroupApproximation
