import GroupApproximation.Higman.PairedReturnCutter
import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.Computability.AdianRabinWordProblem

/-!
# A finite code for the paired-return cutter

`PairedReturnCutter` proves finite presentability of its fixed ambient amalgam
and exhibits the five literal generators of its cutting subgroup.  This file
turns those semantic facts into the exact code-level data consumed by the
effective rope compiler: one `PresentationCode`, an equivalence from its
carrier to the ambient amalgam, and five raw words evaluating to the displayed
cutting elements.

The choices below are made once for this fixed finitely presented group.  They
are therefore constant, hence computable, when inserted into a uniform
compiler; no choice depends on the source program code.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnCutterCode

open PresentationCodes
open PairedReturnCutter
open AdianRabinWordProblem
open Conj

/-- A concrete code naming the fixed paired-return ambient amalgam. -/
noncomputable def ambientCode : PresentationCode := by
  letI : Group.IsFinitelyPresented Ambient := ambient_finitelyPresented
  exact (exists_code_mulEquiv Ambient).choose

/-- The relator set interpreted by the fixed ambient code. -/
abbrev ambientRels : Set (FreeGroup (Fin (genCount ambientCode))) :=
  ((relatorFinset ambientCode : Finset (FreeGroup (Fin (genCount ambientCode)))) :
    Set (FreeGroup (Fin (genCount ambientCode))))

/-- The semantic identification carried by `ambientCode`. -/
noncomputable def ambientEquiv : Carrier ambientCode ≃* Ambient := by
  letI : Group.IsFinitelyPresented Ambient := ambient_finitelyPresented
  exact (exists_code_mulEquiv Ambient).choose_spec.some

/-- Evaluate a raw word in the chosen paired-return presentation. -/
noncomputable def evalRaw (u : List (ℕ × Bool)) : Ambient :=
  ambientEquiv
    (PresentedGroup.mk ambientRels (wordOf ambientCode u))

/-- Every element of the paired-return ambient has a raw representative in
the chosen code. -/
theorem evalRaw_surjective : Function.Surjective evalRaw := by
  exact ambientEquiv.surjective.comp
    ((PresentedGroup.mk_surjective ambientRels).comp
      (wordOf_surjective ambientCode))

/-- A fixed raw representative of an ambient element. -/
noncomputable def rawOf (g : Ambient) : List (ℕ × Bool) :=
  Function.surjInv evalRaw_surjective g

@[simp] theorem evalRaw_rawOf (g : Ambient) : evalRaw (rawOf g) = g :=
  Function.surjInv_eq evalRaw_surjective g

/-- Raw representatives of `x, p_b, p_c, q_b, q_c`, in the exact order of
`PairedReturnCutter.fiveList`. -/
noncomputable def fiveWords : List (List (ℕ × Bool)) :=
  PairedReturnCutter.fiveList.map rawOf

@[simp] theorem fiveWords_length : fiveWords.length = 5 := by
  simp [fiveWords, PairedReturnCutter.fiveList]

/-- The five raw words evaluate to the literal semantic cutting list. -/
theorem fiveWords_map_evalRaw : fiveWords.map evalRaw = PairedReturnCutter.fiveList := by
  simp only [fiveWords, PairedReturnCutter.fiveList, List.map_cons, List.map_nil,
    evalRaw_rawOf]

/-- Pointwise form used when proving the generated-subgroup equality. -/
theorem evalRaw_mem_fiveWords_iff (g : Ambient) :
    g ∈ fiveWords.map evalRaw ↔ g ∈ PairedReturnCutter.fiveList := by
  rw [fiveWords_map_evalRaw]

/-- The raw representatives generate exactly the literal paired-return
cutting subgroup after semantic evaluation. -/
theorem closure_evalRaw_fiveWords :
    Subgroup.closure {g : Ambient | g ∈ fiveWords.map evalRaw} =
      PairedReturnCutter.fiveCutter := by
  rw [fiveWords_map_evalRaw, PairedReturnCutter.setOf_mem_fiveList_eq_fiveSet]
  rfl

/-- The fixed ambient code is a computable constant. -/
theorem computable_ambientCode :
    Computable (fun _ : PUnit => ambientCode) :=
  Computable.const _

/-- The fixed five-word cutting list is a computable constant. -/
theorem computable_fiveWords :
    Computable (fun _ : PUnit => fiveWords) :=
  Computable.const _

/-! ## The six-generator left vertex interface -/

/-- A fixed code for the left vertex `P = F₃ × F₃`. -/
noncomputable def pCode : PresentationCode :=
  (exists_code_mulEquiv PairedReturnGraphIntersection.P).choose

/-- The semantic identification of the fixed left-vertex code. -/
noncomputable def pEquiv :
    Carrier pCode ≃* PairedReturnGraphIntersection.P :=
  (exists_code_mulEquiv PairedReturnGraphIntersection.P).choose_spec.some

abbrev pRels : Set (FreeGroup (Fin (genCount pCode))) :=
  ((relatorFinset pCode : Finset (FreeGroup (Fin (genCount pCode)))) :
    Set (FreeGroup (Fin (genCount pCode))))

/-- Evaluate a raw word in the chosen code for `P`. -/
noncomputable def evalPRaw (u : List (ℕ × Bool)) :
    PairedReturnGraphIntersection.P :=
  pEquiv (PresentedGroup.mk pRels (wordOf pCode u))

theorem evalPRaw_surjective : Function.Surjective evalPRaw := by
  exact pEquiv.surjective.comp
    ((PresentedGroup.mk_surjective pRels).comp (wordOf_surjective pCode))

/-- A fixed raw representative of an element of `P`. -/
noncomputable def pRawOf (g : PairedReturnGraphIntersection.P) :
    List (ℕ × Bool) :=
  Function.surjInv evalPRaw_surjective g

@[simp] theorem evalPRaw_pRawOf (g : PairedReturnGraphIntersection.P) :
    evalPRaw (pRawOf g) = g :=
  Function.surjInv_eq evalPRaw_surjective g

/-- The canonical six generators of `F₃ × F₃`, first the three left-copy
generators and then the three right-copy generators. -/
def pGenerators : List PairedReturnGraphIntersection.P :=
  [((FreeGroup.of 0, 1) : F₃ × F₃),
    ((FreeGroup.of 1, 1) : F₃ × F₃),
    ((FreeGroup.of 2, 1) : F₃ × F₃),
    ((1, FreeGroup.of 0) : F₃ × F₃),
    ((1, FreeGroup.of 1) : F₃ × F₃),
    ((1, FreeGroup.of 2) : F₃ × F₃)]

@[simp] theorem pGenerators_length : pGenerators.length = 6 := rfl

/-- Raw representatives of the six canonical generators in `pCode`. -/
noncomputable def pGeneratorWords : List (List (ℕ × Bool)) :=
  pGenerators.map pRawOf

/-- Raw representatives of their images in the paired-return ambient code. -/
noncomputable def ambientPGeneratorWords : List (List (ℕ × Bool)) :=
  pGenerators.map fun g =>
    rawOf (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g)

/-- The six source/lift pairs exposed to subsequent effective transport
layers. -/
noncomputable def pMarkedWords :
    List (List (ℕ × Bool) × List (ℕ × Bool)) :=
  pGenerators.map fun g =>
    (pRawOf g, rawOf (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g))

@[simp] theorem pGeneratorWords_length : pGeneratorWords.length = 6 := by
  simp [pGeneratorWords]

@[simp] theorem ambientPGeneratorWords_length :
    ambientPGeneratorWords.length = 6 := by
  simp [ambientPGeneratorWords]

@[simp] theorem pMarkedWords_length : pMarkedWords.length = 6 := by
  simp [pMarkedWords]

theorem map_evalPRaw_map_pRawOf
    (l : List PairedReturnGraphIntersection.P) :
    (l.map pRawOf).map evalPRaw = l := by
  induction l with
  | nil => rfl
  | cons g l ih => simp only [List.map_cons, evalPRaw_pRawOf, ih]

theorem pGeneratorWords_map_evalPRaw :
    pGeneratorWords.map evalPRaw = pGenerators := by
  exact map_evalPRaw_map_pRawOf pGenerators

theorem map_evalRaw_map_ambientRawOf
    (l : List PairedReturnGraphIntersection.P) :
    (l.map fun g => rawOf
      (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC g)).map evalRaw =
        l.map (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC) := by
  induction l with
  | nil => rfl
  | cons g l ih => simp only [List.map_cons, evalRaw_rawOf, ih]

theorem ambientPGeneratorWords_map_evalRaw :
    ambientPGeneratorWords.map evalRaw =
      pGenerators.map (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC) := by
  exact map_evalRaw_map_ambientRawOf pGenerators

/-- Each of the six marked pairs evaluates compatibly with the embedded left
vertex. -/
theorem pMarkedWords_compatible
    (pair : List (ℕ × Bool) × List (ℕ × Bool))
    (hpair : pair ∈ pMarkedWords) :
    evalRaw pair.2 =
      MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (evalPRaw pair.1) := by
  simp only [pMarkedWords, List.mem_map] at hpair
  obtain ⟨g, -, rfl⟩ := hpair
  rw [evalRaw_rawOf, evalPRaw_pRawOf]

theorem computable_pCode : Computable (fun _ : PUnit => pCode) :=
  Computable.const _

theorem computable_pGeneratorWords :
    Computable (fun _ : PUnit => pGeneratorWords) :=
  Computable.const _

theorem computable_ambientPGeneratorWords :
    Computable (fun _ : PUnit => ambientPGeneratorWords) :=
  Computable.const _

theorem computable_pMarkedWords :
    Computable (fun _ : PUnit => pMarkedWords) :=
  Computable.const _

end PairedReturnCutterCode
end Higman
end GroupApproximation
