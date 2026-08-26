import GroupApproximation.Higman.ExplicitFreeEdge

/-!
# An injected free-edge compiler tower

This file composes the honest HNN extensions from `ExplicitFreeEdge`.
There is no appeal to an embedding theorem: Mathlib's Britton normal form
gives injectivity of the base map at each individual HNN edge, and ordinary
composition gives injectivity through the whole tower.

The intended order is

* one shear edge for every `tau_j`;
* the `d` edge;
* the `sigma` edge;
* the corrected conjugated centralizer detector, attached last.

Every edge is stored as `ExplicitFreeEdge.Data`.  Consequently its only
non-formal obligations are the two visibly displayed free-group evaluation
maps and proofs that those maps are injective.  The constructors
`evaluatedShearData`, `dData`, and `sigmaData` expose those obligations.  The
list-indexed `MarkedStage` additionally remembers every stable letter, in the
same order as the raw finite-presentation compiler.
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

/-! ## Arbitrarily composable, marked HNN edges -/

/-- A group reached from `G` by `n` explicitly injected HNN edges, together
with the stable letter contributed by every edge. -/
structure MarkedStage (G : Type) [Group G] (n : ℕ) where
  Carrier : Type
  group : Group Carrier
  map : G →* Carrier
  map_injective : Function.Injective map
  stable : Fin n → Carrier

attribute [instance] MarkedStage.group

/-- The empty chain. -/
def MarkedStage.base (G : Type) [Group G] : MarkedStage G 0 where
  Carrier := G
  group := inferInstance
  map := MonoidHom.id G
  map_injective := Function.injective_id
  stable := Fin.elim0

/-- Add one honest free-edge HNN extension.  Old stable letters are transported
by the base inclusion and the new stable letter occupies the final index. -/
def MarkedStage.addEdge {n : ℕ} (S : MarkedStage G n) {X : Type}
    (E : Data X S.Carrier) : MarkedStage G (n + 1) where
  Carrier := Extension E
  group := inferInstance
  map := (of : S.Carrier →* Extension E).comp S.map
  map_injective :=
    (HNNExtension.of_injective (φ := edgeEquiv E)).comp S.map_injective
  stable := Fin.lastCases t (fun i => of (S.stable i))

@[simp] theorem MarkedStage.addEdge_stable_castSucc {n : ℕ}
    (S : MarkedStage G n) {X : Type} (E : Data X S.Carrier) (i : Fin n) :
    (S.addEdge E).stable i.castSucc = of (S.stable i) := by
  simp [MarkedStage.addEdge]

@[simp] theorem MarkedStage.addEdge_stable_last {n : ℕ}
    (S : MarkedStage G n) {X : Type} (E : Data X S.Carrier) :
    (S.addEdge E).stable (Fin.last n) = t := by
  simp [MarkedStage.addEdge]

/-! ## A compiler tower over an arbitrary injected `tau_j` chain -/

/-- The general inner compiler.  `tauStage` is built by starting from
`MarkedStage.base` and calling `MarkedStage.addEdge` once for every
`tau_j`; the remaining two fields are the `d` and `sigma` edges. -/
structure CompilerTower (G : Type) [Group G] (tauCount : ℕ) where
  tauStage : MarkedStage G tauCount
  DIndex : Type
  d : Data DIndex tauStage.Carrier
  SigmaIndex : Type
  sigma : Data SigmaIndex (Extension d)

variable {tauCount : ℕ} (C : CompilerTower G tauCount)

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

/-- The `i`-th `tau` stable letter transported through `d` and `sigma`. -/
def compilerTauStable (i : Fin tauCount) : CompilerTop C :=
  compilerDToTop C (compilerTauToD C (C.tauStage.stable i))

/-! ## The corrected detector, attached after the tower -/

variable {F K : Type} [Group F] [Group K]

/-- A compiler whose starting group is `K * ⟨q⟩`, realized as the HNN
extension of `K` over the trivial subgroup. -/
abbrev FreeLetterTower (tauCount : ℕ) :=
  CompilerTower (ConjugatedDetector.FreeLetterExtension K) tauCount

/-- The final central HNN detector, attached only after `tau`, `d`, and
`sigma` have been completed. -/
abbrev Outermost {tauCount : ℕ} (L : Subgroup K)
    (T : FreeLetterTower (K := K) tauCount) : Type _ :=
  ConjugatedDetector.FreeOutermostExtension L (compilerBaseToTop T)

/-- The completed inner tower embeds in the outermost detector. -/
def topToOutermost {tauCount : ℕ} (L : Subgroup K)
    (T : FreeLetterTower (K := K) tauCount) :
    CompilerTop T →* Outermost L T := of

/-- The free-letter base mapped through the `tau_j` family, `d`, `sigma`, and
the outer detector. -/
def freeLetterToOutermost (L : Subgroup K)
  {tauCount : ℕ} (T : FreeLetterTower (K := K) tauCount) :
    ConjugatedDetector.FreeLetterExtension K →* Outermost L T :=
  (topToOutermost L T).comp (compilerBaseToTop T)

/-- The original benign-witness ambient group mapped through the free-letter
step, the whole compiler tower, and the final detector. -/
def originalToOutermost (L : Subgroup K)
    {tauCount : ℕ} (T : FreeLetterTower (K := K) tauCount) :
    K →* Outermost L T :=
  (freeLetterToOutermost L T).comp
    (of : K →* ConjugatedDetector.FreeLetterExtension K)

/-- Britton injectivity for the final, central detector edge. -/
theorem topToOutermost_injective (L : Subgroup K)
    {tauCount : ℕ} (T : FreeLetterTower (K := K) tauCount) :
    Function.Injective (topToOutermost L T) :=
  of_injective_centHNN _

/-- The free-letter base survives the complete construction. -/
theorem freeLetterToOutermost_injective (L : Subgroup K)
    {tauCount : ℕ} (T : FreeLetterTower (K := K) tauCount) :
    Function.Injective (freeLetterToOutermost L T) :=
  (topToOutermost_injective L T).comp (compilerBaseToTop_injective T)

/-- In particular the original benign-witness ambient group survives the
complete tower. -/
theorem originalToOutermost_injective (L : Subgroup K)
    {tauCount : ℕ} (T : FreeLetterTower (K := K) tauCount) :
    Function.Injective (originalToOutermost L T) :=
  (freeLetterToOutermost_injective L T).comp
    (of_injective_centHNN (⊥ : Subgroup K))

/-- The corrected edge subgroup remains disjoint from the old embedded copy
of `F` at the top of the inner tower. -/
theorem detectorEdge_inf_embedded_atTop
    (L : Subgroup K) (e : F →* K) {tauCount : ℕ}
    (T : FreeLetterTower (K := K) tauCount) :
    (ConjugatedDetector.freeLetterConjugateSubgroup L).map (compilerBaseToTop T) ⊓
        (ConjugatedDetector.freeLetterEmbeddedSubgroup e).map
          (compilerBaseToTop T) = ⊥ :=
  ConjugatedDetector.tower_freeLetterConjugate_inf_embedded
    L e (compilerBaseToTop T) (compilerBaseToTop_injective T)

/-- The literal payload tested by the outermost stable letter. -/
def detectedWord (L : Subgroup K) (e : F →* K)
    {tauCount : ℕ} (T : FreeLetterTower (K := K) tauCount)
    (f : F) : Outermost L T :=
  ConjugatedDetector.freeDetectedWord L e (compilerBaseToTop T) f

/-- **End-to-end detector survival.**

Start with a subgroup cut `L.comap e = N`, adjoin the free conjugating letter,
pass through the explicit `tau_j`, `d`, and `sigma` HNN edges, and only then
adjoin the detector.  Every intervening base map is injective by Britton's
lemma.  Therefore the final stable letter commutes with the transported word
exactly for the elements of `N`.

No compiler theorem or literature result occurs among the assumptions.  To
build the inner tower with `MarkedStage.addEdge`, the remaining obligations at
each edge are exactly the displayed `source_injective` and `target_injective`
fields of `ExplicitFreeEdge.Data`. -/
theorem commute_outerStable_detectedWord_iff
    (N : Subgroup F) (L : Subgroup K) (e : F →* K)
    {tauCount : ℕ} (T : FreeLetterTower (K := K) tauCount)
    (hcut : L.comap e = N) (f : F) :
    Commute (t : Outermost L T) (detectedWord L e T f) ↔ f ∈ N := by
  exact ConjugatedDetector.commute_freeStable_freeDetectedWord_iff
    N L e (compilerBaseToTop T) (compilerBaseToTop_injective T) hcut f

end

end InjectedCompilerTower
end Higman
end GroupApproximation
