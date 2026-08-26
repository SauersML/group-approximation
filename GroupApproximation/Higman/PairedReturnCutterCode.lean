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

end PairedReturnCutterCode
end Higman
end GroupApproximation
