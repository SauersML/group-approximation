import GroupApproximation.Computability.FreeEdgeTowerCodePrimrec
import GroupApproximation.Computability.FreeEdgeTowerExactIteration

/-!
# A computable marked output from the exact free-edge compiler

The finite presentation and its three raw marks are syntactic and computable;
the exact-chain semantics prove that those literal marks carry the first three
base generators injectively into the compiled group.
-/

namespace GroupApproximation
namespace FreeEdgeTowerMarkedCompiler

open PresentationCodes FreeEdgeTowerCode
open FreeEdgeTowerExactIteration

abbrev Raw := List (ℕ × Bool)

/-- Finite presentation plus three marked raw words. -/
abbrev Output : Type := PresentationCode × Raw × Raw × Raw

/-- The one-letter mark for source generator `i`. -/
def rankThreeWord (i : Fin 3) : Raw := [((i : ℕ), true)]

/-- Concrete marked syntax emitted by a tower input. -/
def compileMarked (x : TowerInput) : Output :=
  (compile x, rankThreeWord 0, rankThreeWord 1, rankThreeWord 2)

theorem primrec_rankThreeWord :
    Primrec rankThreeWord :=
  Primrec.list_cons.comp
    (Primrec.pair Primrec.fin_val (Primrec.const true)) (Primrec.const [])

/-- The marked finite-output compiler is primitive recursive. -/
theorem primrec_compileMarked : Primrec compileMarked := by
  have hzero : Primrec (fun _ : TowerInput => rankThreeWord 0) := Primrec.const _
  have hone : Primrec (fun _ : TowerInput => rankThreeWord 1) := Primrec.const _
  have htwo : Primrec (fun _ : TowerInput => rankThreeWord 2) := Primrec.const _
  exact Primrec.pair FreeEdgeTowerCode.primrec_compile
    (Primrec.pair hzero (Primrec.pair hone htwo))

theorem computable_compileMarked : Computable compileMarked :=
  primrec_compileMarked.to_comp

/-- View the three distinguished positions as generators of the base code. -/
def baseIndex (x : TowerInput) (h3 : 3 ≤ genCount x.1) (i : Fin 3) :
    Fin (genCount x.1) :=
  ⟨i, i.isLt.trans_le h3⟩

@[simp] theorem baseIndex_val (x : TowerInput) (h3 : 3 ≤ genCount x.1)
    (i : Fin 3) : (baseIndex x h3 i : ℕ) = i := rfl

/-- **Concrete marked semantics.**  Each of the three literal output words
evaluates to the image of its corresponding base generator. -/
theorem compilerEmbedding_eq_rankThreeWord (x : TowerInput)
    (h : ExactChain x.1 (innerCompilerLayers x))
    (h3 : 3 ≤ genCount x.1) (i : Fin 3) :
    compilerEmbedding x h (PresentedGroup.of (baseIndex x h3 i)) =
      compiledWord x (rankThreeWord i) := by
  simpa only [rankThreeWord, compilerMarkedWord, baseIndex_val] using
    compilerEmbedding_eq_compiledWord x h (baseIndex x h3 i)

end FreeEdgeTowerMarkedCompiler
end GroupApproximation
