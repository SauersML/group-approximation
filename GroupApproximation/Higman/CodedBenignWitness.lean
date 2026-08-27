import GroupApproximation.Higman.BenignTorsionFree
import GroupApproximation.Computability.BenignInfCodeSubgroupSemantics
import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.Computability.AdianRabinWordProblem

/-!
# Finite syntax for an arbitrary fixed benign witness

A benign witness already contains exactly the finiteness needed by the code
layer: its ambient group is finitely presented and its cutter is finitely
generated.  This file chooses, once and for all, a presentation code, raw
representatives of cutter generators, and raw representatives of six marked
source elements.  The construction is noncomputable as a function of an
abstract witness, but every specialization to a fixed witness is a constant
and hence is a valid computable constant in the uniform Higman compiler.
-/

namespace GroupApproximation
namespace Higman
namespace CodedBenignWitness

noncomputable section

open PresentationCodes BenignInfCode
open BenignInfCodeSemantics BenignInfCodeSubgroupSemantics
open AdianRabinWordProblem

abbrev MarkCount := Fin 6
abbrev WitnessSyntax := BenignInfCode.WitnessSyntax

/-- The semantic contract carried by finite benign-witness syntax. -/
structure Model {G : Type} [Group G] (mark : MarkCount → G)
    (H : Subgroup G) where
  data : BenignWitness H
  coded : WitnessSyntax
  ambientEquiv : Carrier coded.1 ≃* data.K
  cutter_eq :
    (wordSubgroup coded.1 coded.2.1).map ambientEquiv.toMonoidHom = data.L
  marked_eq : ∀ i : MarkCount,
    ambientEquiv (evalWord coded.1 (coded.2.2.getD i [])) = data.emb (mark i)

variable {G : Type} [Group G] {H : Subgroup G}

/-- A presentation code for the finitely presented witness ambient. -/
noncomputable def ambientCode (w : BenignWitness H) : PresentationCode :=
  (exists_code_mulEquiv w.K).choose

/-- The chosen code presents the witness ambient. -/
noncomputable def ambientEquiv (w : BenignWitness H) :
    Carrier (ambientCode w) ≃* w.K :=
  (exists_code_mulEquiv w.K).choose_spec.some

noncomputable def evalRaw (w : BenignWitness H) (u : List (ℕ × Bool)) : w.K :=
  ambientEquiv w (evalWord (ambientCode w) u)

theorem evalRaw_surjective (w : BenignWitness H) :
    Function.Surjective (evalRaw w) := by
  exact (ambientEquiv w).surjective.comp
    ((PresentedGroup.mk_surjective
      (DirectProductCodeSemantics.codeRels (ambientCode w))).comp
        (wordOf_surjective (ambientCode w)))

noncomputable def rawOf (w : BenignWitness H) (g : w.K) : List (ℕ × Bool) :=
  Function.surjInv (evalRaw_surjective w) g

@[simp] theorem evalRaw_rawOf (w : BenignWitness H) (g : w.K) :
    evalRaw w (rawOf w g) = g :=
  Function.surjInv_eq (evalRaw_surjective w) g

/-- A finite set whose closure is the witness cutter. -/
noncomputable def cutterSet (w : BenignWitness H) : Set w.K :=
  ((Subgroup.fg_iff w.L).mp w.L_fg).choose

theorem closure_cutterSet (w : BenignWitness H) :
    Subgroup.closure (cutterSet w) = w.L :=
  ((Subgroup.fg_iff w.L).mp w.L_fg).choose_spec.1

theorem cutterSet_finite (w : BenignWitness H) : (cutterSet w).Finite :=
  ((Subgroup.fg_iff w.L).mp w.L_fg).choose_spec.2

noncomputable def cutterElements (w : BenignWitness H) : List w.K :=
  (cutterSet_finite w).toFinset.toList

theorem mem_cutterElements_iff (w : BenignWitness H) (g : w.K) :
    g ∈ cutterElements w ↔ g ∈ cutterSet w := by
  simp [cutterElements]

noncomputable def cutterWords (w : BenignWitness H) : List (List (ℕ × Bool)) :=
  (cutterElements w).map (rawOf w)

noncomputable def markedWords (mark : MarkCount → G) (w : BenignWitness H) :
    List (List (ℕ × Bool)) :=
  [rawOf w (w.emb (mark 0)), rawOf w (w.emb (mark 1)),
    rawOf w (w.emb (mark 2)), rawOf w (w.emb (mark 3)),
    rawOf w (w.emb (mark 4)), rawOf w (w.emb (mark 5))]

noncomputable def codedSyntax (mark : MarkCount → G) (w : BenignWitness H) :
    WitnessSyntax :=
  (ambientCode w, (cutterWords w, markedWords mark w))

theorem image_evalWord_cutterWords (w : BenignWitness H) :
    (ambientEquiv w).toMonoidHom ''
        {g | ∃ u ∈ cutterWords w, evalWord (ambientCode w) u = g} =
      cutterSet w := by
  ext g
  constructor
  · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
    change evalRaw w (rawOf w k) ∈ cutterSet w
    rw [evalRaw_rawOf]
    exact (mem_cutterElements_iff w k).mp hk
  · intro hg
    have hglist : g ∈ cutterElements w :=
      (mem_cutterElements_iff w g).mpr hg
    refine ⟨evalWord (ambientCode w) (rawOf w g), ?_, ?_⟩
    · exact ⟨rawOf w g, List.mem_map.mpr ⟨g, hglist, rfl⟩, rfl⟩
    · exact evalRaw_rawOf w g

theorem map_wordSubgroup_cutterWords (w : BenignWitness H) :
    (wordSubgroup (ambientCode w) (cutterWords w)).map
        (ambientEquiv w).toMonoidHom = w.L := by
  rw [wordSubgroup, MonoidHom.map_closure, image_evalWord_cutterWords,
    closure_cutterSet]

/-- Every abstract benign witness admits exact six-mark finite syntax. -/
noncomputable def model (mark : MarkCount → G) (w : BenignWitness H) :
    Model mark H where
  data := w
  coded := codedSyntax mark w
  ambientEquiv := ambientEquiv w
  cutter_eq := map_wordSubgroup_cutterWords w
  marked_eq := by
    intro i
    fin_cases i <;>
      change evalRaw w (rawOf w (w.emb (mark _))) = w.emb (mark _) <;>
      exact evalRaw_rawOf w _

/-- A fixed encoded witness is a computable constant. -/
theorem computable_codedSyntax (mark : MarkCount → G) (w : BenignWitness H) :
    Computable (fun _ : PUnit => codedSyntax mark w) :=
  Computable.const _

end

end CodedBenignWitness
end Higman
end GroupApproximation
