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

noncomputable section

variable {G : Type} [Group G]

/-! ## A shear transported through a free evaluation map -/

/-- The Nielsen shear remains injective before it is evaluated in a base
group. -/
theorem shearForward_injective {X : Type} (payload : FreeGroup X) :
    Function.Injective (shearForward payload) := by
  intro a b hab
  have h := congrArg (shearBackward payload) hab
  simpa only [← MonoidHom.comp_apply,
    shearBackward_comp_shearForward, MonoidHom.id_apply] using h

/-- Evaluate both sides of the Nielsen shear in an arbitrary group.  The
target is injective for formal reasons once the displayed source evaluation
is injective. -/
def evaluatedShearData {X : Type}
    (eval : FreeGroup (X ⊕ Unit) →* G) (heval : Function.Injective eval)
    (payload : FreeGroup X) : Data (X ⊕ Unit) G where
  source := eval
  target := eval.comp (shearForward payload)
  source_injective := heval
  target_injective := heval.comp (shearForward_injective payload)

@[simp] theorem evaluatedShearData_source {X : Type}
    (eval : FreeGroup (X ⊕ Unit) →* G) (heval : Function.Injective eval)
    (payload : FreeGroup X) :
    (evaluatedShearData eval heval payload).source = eval := rfl

@[simp] theorem evaluatedShearData_target {X : Type}
    (eval : FreeGroup (X ⊕ Unit) →* G) (heval : Function.Injective eval)
    (payload : FreeGroup X) :
    (evaluatedShearData eval heval payload).target =
      eval.comp (shearForward payload) := rfl

/-- The stable letter of the evaluated shear carries every source word to
its Nielsen-sheared evaluation. -/
theorem evaluatedShear_stable_conj {X : Type}
    (eval : FreeGroup (X ⊕ Unit) →* G) (heval : Function.Injective eval)
    (payload : FreeGroup X) (word : FreeGroup (X ⊕ Unit)) :
    (t : Extension (evaluatedShearData eval heval payload)) *
        of (eval word) * t⁻¹ = of (eval (shearForward payload word)) := by
  simpa [evaluatedShearData] using
    stable_conj_source (evaluatedShearData eval heval payload) word

/-! ## Arbitrarily composable HNN edges -/

/-- A group reached from `G` by an explicitly injected chain. -/
structure InjectedStage (G : Type) [Group G] where
  Carrier : Type
  group : Group Carrier
  map : G →* Carrier
  map_injective : Function.Injective map

attribute [instance] InjectedStage.group

/-- The empty chain. -/
def InjectedStage.base (G : Type) [Group G] : InjectedStage G where
  Carrier := G
  group := inferInstance
  map := MonoidHom.id G
  map_injective := Function.injective_id

/-- Add one honest free-edge HNN extension to an injected chain. -/
def InjectedStage.addEdge (S : InjectedStage G) {X : Type}
    (E : Data X S.Carrier) : InjectedStage G where
  Carrier := Extension E
  group := inferInstance
  map := (of : S.Carrier →* Extension E).comp S.map
  map_injective :=
    (HNNExtension.of_injective (φ := edgeEquiv E)).comp S.map_injective

/-! ## The singleton-`tau` specialization -/

/-- The exact algebraic data of the three inner compiler layers.  Every
field is a concrete `ExplicitFreeEdge.Data`, hence records two homomorphisms
from a displayed free group and injectivity proofs for precisely those maps.
-/
structure SingletonTauThreeStage (G : Type) [Group G] where
  TauIndex : Type
  tau : Data TauIndex G
  DIndex : Type
  d : Data DIndex (Extension tau)
  SigmaIndex : Type
  sigma : Data SigmaIndex (Extension d)

variable (T : SingletonTauThreeStage G)

/-- The group after the `tau` edge. -/
abbrev Tau : Type := Extension T.tau

/-- The group after the `d` edge. -/
abbrev D : Type := Extension T.d

/-- The group after the `sigma` edge. -/
abbrev Top : Type := Extension T.sigma

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

/-! ## The named `tau`--`d`--`sigma` constructor -/

/-- The first layer obtained by evaluating the Nielsen shear. -/
abbrev ShearTau {X : Type}
    (eval : FreeGroup (X ⊕ Unit) →* G) (heval : Function.Injective eval)
    (payload : FreeGroup X) : Type _ :=
  Extension (evaluatedShearData eval heval payload)

/-- The second layer, using the explicit `d` evaluation maps. -/
abbrev ShearD {X J : Type}
    (eval : FreeGroup (X ⊕ Unit) →* G) (heval : Function.Injective eval)
    (payload : FreeGroup X)
    (k0 : ShearTau eval heval payload)
    (s tauLetter : J → ShearTau eval heval payload)
    (hsource : Function.Injective (dSource k0 s tauLetter))
    (htarget : Function.Injective (dTarget k0 s)) : Type _ :=
  Extension (dData k0 s tauLetter hsource htarget)

/-- Build the complete three-layer value from the literal evaluation maps.

The only hypotheses are injectivity of:

* the initial free evaluation `eval`;
* `dSource k0 s tauLetter` and `dTarget k0 s`;
* `sigmaSource fixed t0` and `sigmaTarget fixed t0 d0`.

Injectivity of the sheared target is derived automatically from the Nielsen
inverse. -/
def singletonShearDSigmaTower {X J Y : Type}
    (eval : FreeGroup (X ⊕ Unit) →* G) (heval : Function.Injective eval)
    (payload : FreeGroup X)
    (k0 : ShearTau eval heval payload)
    (s tauLetter : J → ShearTau eval heval payload)
    (hdSource : Function.Injective (dSource k0 s tauLetter))
    (hdTarget : Function.Injective (dTarget k0 s))
    (fixed : Y → ShearD eval heval payload k0 s tauLetter hdSource hdTarget)
    (t0 d0 : ShearD eval heval payload k0 s tauLetter hdSource hdTarget)
    (hsigmaSource : Function.Injective (sigmaSource fixed t0))
    (hsigmaTarget : Function.Injective (sigmaTarget fixed t0 d0)) :
    SingletonTauThreeStage G where
  TauIndex := X ⊕ Unit
  tau := evaluatedShearData eval heval payload
  DIndex := Unit ⊕ J
  d := dData k0 s tauLetter hdSource hdTarget
  SigmaIndex := Y ⊕ Unit
  sigma := sigmaData fixed t0 d0 hsigmaSource hsigmaTarget

/-! ## A compiler tower over an arbitrary injected `tau_j` chain -/

/-- The general inner compiler.  `tauStage` is built by starting from
`InjectedStage.base` and calling `InjectedStage.addEdge` once for every
`tau_j`; the remaining two fields are the `d` and `sigma` edges. -/
structure CompilerTower (G : Type) [Group G] where
  tauStage : InjectedStage G
  DIndex : Type
  d : Data DIndex tauStage.Carrier
  SigmaIndex : Type
  sigma : Data SigmaIndex (Extension d)

variable (C : CompilerTower G)

abbrev CompilerD : Type := Extension C.d

abbrev CompilerTop : Type := Extension C.sigma

def compilerTauToD : C.tauStage.Carrier →* CompilerD C := of

def compilerDToTop : CompilerD C →* CompilerTop C := of

/-- The original base mapped through the entire `tau_j`, `d`, `sigma` chain. -/
def compilerBaseToTop : G →* CompilerTop C :=
  (compilerDToTop C).comp ((compilerTauToD C).comp C.tauStage.map)

theorem compilerTauToD_injective : Function.Injective (compilerTauToD C) :=
  HNNExtension.of_injective (φ := edgeEquiv C.d)

theorem compilerDToTop_injective : Function.Injective (compilerDToTop C) :=
  HNNExtension.of_injective (φ := edgeEquiv C.sigma)

theorem compilerBaseToTop_injective : Function.Injective (compilerBaseToTop C) :=
  (compilerDToTop_injective C).comp
    ((compilerTauToD_injective C).comp C.tauStage.map_injective)

/-! ## The corrected detector, attached after the tower -/

variable {F K : Type} [Group F] [Group K]

/-- A three-stage compiler whose starting group is `K * ⟨q⟩`, realized as
the HNN extension of `K` over the trivial subgroup. -/
abbrev FreeLetterTower := CompilerTower (ConjugatedDetector.FreeLetterExtension K)

/-- The final central HNN detector, attached only after `tau`, `d`, and
`sigma` have been completed. -/
abbrev Outermost (L : Subgroup K) (T : FreeLetterTower (K := K)) : Type _ :=
  ConjugatedDetector.FreeOutermostExtension L (compilerBaseToTop T)

/-- The completed inner tower embeds in the outermost detector. -/
def topToOutermost (L : Subgroup K) (T : FreeLetterTower (K := K)) :
    CompilerTop T →* Outermost L T := of

/-- The free-letter base mapped through all four layers. -/
def freeLetterToOutermost (L : Subgroup K)
  (T : FreeLetterTower (K := K)) :
    ConjugatedDetector.FreeLetterExtension K →* Outermost L T :=
  (topToOutermost L T).comp (compilerBaseToTop T)

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
  (topToOutermost_injective L T).comp (compilerBaseToTop_injective T)

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
    (ConjugatedDetector.freeLetterConjugateSubgroup L).map (compilerBaseToTop T) ⊓
        (ConjugatedDetector.freeLetterEmbeddedSubgroup e).map
          (compilerBaseToTop T) = ⊥ :=
  ConjugatedDetector.tower_freeLetterConjugate_inf_embedded
    L e (compilerBaseToTop T) (compilerBaseToTop_injective T)

/-- The literal payload tested by the outermost stable letter. -/
def detectedWord (L : Subgroup K) (e : F →* K)
    (T : FreeLetterTower (K := K)) (f : F) : Outermost L T :=
  ConjugatedDetector.freeDetectedWord L e (compilerBaseToTop T) f

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
    N L e (compilerBaseToTop T) (compilerBaseToTop_injective T) hcut f

end

end InjectedCompilerTower
end Higman
end GroupApproximation
