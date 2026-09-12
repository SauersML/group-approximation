import GroupApproximation.Higman.MikhailovaGraphProductWitness
import GroupApproximation.Higman.MikhailovaRankThreeProfinite
import GroupApproximation.Higman.ProfiniteBenignWitness
import GroupApproximation.Sofic.FreeGroupResiduallyFinite

/-!
# Profinite Mikhailova--graph product witnesses

The two factors used by the concrete rank-three compiler carry stronger
profinite data for elementary, split reasons.  The Mikhailova marked source
and the graph source are both retracted by first projection.  The graph
cutting subgroup is itself the range of a section of first projection, while
the Mikhailova cutter is closed whenever its presented quotient is residually
finite.  Their intersection therefore uses only the unconditional direct
product operation on `ProfiniteBenignWitness`.
-/

namespace GroupApproximation
namespace Higman
namespace MikhailovaGraphProductProfinite

noncomputable section

open MikhailovaRankThree
open MikhailovaGraphProduct

/-- First projection retracts the graph cutting map. -/
theorem fst_comp_graphHom {P : Type} [Group P] (q : Source →* P) :
    (MonoidHom.fst Source P).comp (graphHom q) = MonoidHom.id Source := by
  ext f
  rfl

/-- The graph cutter and the marked first-factor embedding have all the
profinite properties required by the compiler. -/
def graphKernelWitness {P : Type} [Group P]
    [Group.IsFinitelyPresented P] [Group.ResiduallyFinite P]
    (q : Source →* P) : ProfiniteBenignWitness q.ker where
  witness := MikhailovaGraphProduct.graphKernelWitness q
  ambientRF := by
    change Group.ResiduallyFinite (Source × P)
    infer_instance
  cutterClosed := by
    exact profiniteClosure_range_eq_range_of_retraction
      (graphHom q) (MonoidHom.fst Source P) (fst_comp_graphHom q)
  embCofinal := by
    change CofinalProfiniteEmbedding (graphInput (P := P))
    exact CofinalProfiniteEmbedding.postcomp_of_retraction
      CofinalProfiniteEmbedding.id (graphInput (P := P))
      (MonoidHom.fst Source P) (by ext f; rfl)
  embClosed := by
    change profiniteClosure (graphInput (P := P)).range =
      (graphInput (P := P)).range
    letI : Group.ResiduallyFinite (Source × P) := inferInstance
    exact profiniteClosure_range_eq_range_of_retraction
      (graphInput (P := P)) (MonoidHom.fst Source P) (by ext f; rfl)

/-- Composing the graph coordinate with an embedding into an RF finitely
presented group changes no profinite argument. -/
def embeddedGraphKernelWitness {Q P : Type} [Group Q] [Group P]
    [Group.IsFinitelyPresented P] [Group.ResiduallyFinite P]
    (q : Source →* Q) (j : Q →* P) (hj : Function.Injective j) :
    ProfiniteBenignWitness q.ker := by
  let u : ProfiniteBenignWitness (j.comp q).ker :=
    MikhailovaGraphProductProfinite.graphKernelWitness (j.comp q)
  rw [ker_comp_eq_of_injective q j hj] at u
  exact u

/-- Positive-branch profinite upgrade of the rank-three Mikhailova witness. -/
def normalClosureWitnessOfMarkedEmbedding
    {X : Type} [Finite X] (S : Set Source) {R : Set (FreeGroup X)}
    (hR : R.Finite) (words : Source →* FreeGroup X)
    (i : PresentedGroup S →* PresentedGroup R) (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S))
    [Group.ResiduallyFinite (PresentedGroup R)] :
    ProfiniteBenignWitness (Subgroup.normalClosure S) where
  witness := MikhailovaRankThree.normalClosureWitnessOfMarkedEmbedding
    S hR words i hi hcomm
  ambientRF := by
    change Group.ResiduallyFinite (MikhailovaRankThree.Ambient X)
    infer_instance
  cutterClosed := by
    letI : Group.ResiduallyFinite
        (FreeGroup X ⧸ Subgroup.normalClosure R) := by
      change Group.ResiduallyFinite (PresentedGroup R)
      infer_instance
    exact MikhailovaRankThree.profiniteClosure_cuttingSubgroup R
  embCofinal :=
    CofinalProfiniteEmbedding.postcomp_of_retraction
      CofinalProfiniteEmbedding.id (inputHom words) inputProjection
      (inputProjection_comp_inputHom words)
  embClosed := MikhailovaRankThree.profiniteClosure_inputHom_range words

/-- The exact positive-branch product witness used by the compiler. -/
def normalClosureProductWitness
    {X P : Type} [Finite X] [Group P] [Group.IsFinitelyPresented P]
    [Group.ResiduallyFinite P]
    (S : Set Source) {R : Set (FreeGroup X)} (hR : R.Finite)
    (words : Source →* FreeGroup X)
    (i : PresentedGroup S →* PresentedGroup R) (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S))
    [Group.ResiduallyFinite (PresentedGroup R)]
    (q : Source →* P) (hSq : Subgroup.normalClosure S ≤ q.ker) :
    ProfiniteBenignWitness (Subgroup.normalClosure S) := by
  let wm : ProfiniteBenignWitness (Subgroup.normalClosure S) :=
    MikhailovaGraphProductProfinite.normalClosureWitnessOfMarkedEmbedding
      S hR words i hi hcomm
  let wg : ProfiniteBenignWitness q.ker :=
    MikhailovaGraphProductProfinite.graphKernelWitness q
  have heq : Subgroup.normalClosure S ⊓ q.ker =
      Subgroup.normalClosure S := inf_eq_left.mpr hSq
  rw [← heq]
  exact wm.inf wg

/-- Embedded-graph variant of the same positive-branch product witness. -/
def normalClosureProductWitnessOfEmbeddedGraph
    {X Q P : Type} [Finite X] [Group Q] [Group P]
    [Group.IsFinitelyPresented P] [Group.ResiduallyFinite P]
    (S : Set Source) {R : Set (FreeGroup X)} (hR : R.Finite)
    (words : Source →* FreeGroup X)
    (i : PresentedGroup S →* PresentedGroup R) (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S))
    [Group.ResiduallyFinite (PresentedGroup R)]
    (q : Source →* Q) (j : Q →* P) (hj : Function.Injective j)
    (hSq : Subgroup.normalClosure S ≤ q.ker) :
    ProfiniteBenignWitness (Subgroup.normalClosure S) := by
  let wm : ProfiniteBenignWitness (Subgroup.normalClosure S) :=
    MikhailovaGraphProductProfinite.normalClosureWitnessOfMarkedEmbedding
      S hR words i hi hcomm
  let wg : ProfiniteBenignWitness q.ker :=
    MikhailovaGraphProductProfinite.embeddedGraphKernelWitness q j hj
  have heq : Subgroup.normalClosure S ⊓ q.ker =
      Subgroup.normalClosure S := inf_eq_left.mpr hSq
  rw [← heq]
  exact wm.inf wg

end

end MikhailovaGraphProductProfinite
end Higman
end GroupApproximation
