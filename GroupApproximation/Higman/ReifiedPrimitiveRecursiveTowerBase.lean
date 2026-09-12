import GroupApproximation.Computability.FreeEdgeTowerMarkedCompiler
import GroupApproximation.Higman.ReifiedPrimitiveRecursiveCode

/-!
# The first concrete tower input for the reified Higman compiler

Higman's zero base is `A_Z = ⟨a⟩` inside the free group on `a,b,c`.
Consequently its finite detector input is completely literal: start with the
three-generator free presentation, use no `tau` edges, use empty `d` and
`sigma` edges, and centralize the one-letter word spelling `a`.

This is not a caller-supplied interface.  It is an actual `TowerInput`, its
inner exact chain is closed below, and the existing marked compiler therefore
emits a finite presentation with three literal words carrying the embedded
free rank-three base.
-/

namespace GroupApproximation
namespace Higman
namespace ReifiedPrimrecTower

open PresentationCodes FreeEdgeTowerCode
open FreeEdgeTowerExactIteration FreeEdgeTowerMarkedCompiler

/-- The free rank-three presentation used by Higman's sequence calculus. -/
def rankThreeBaseCode : PresentationCode := (2, [])

/-- The literal word spelling the first free generator `a`. -/
def aWord : FreeEdgeTowerCode.Raw := [((0 : ℕ), true)]

/-- **Concrete zero-base tower input.**  The final edge centralizes `a`; the
two compulsory inner slots are empty exact edges. -/
def zeroBaseInput : TowerInput :=
  (rankThreeBaseCode, ([], ([], ([], [aWord]))))

@[simp] theorem zeroBaseInput_genCount : genCount zeroBaseInput.1 = 3 := by
  simp [zeroBaseInput, rankThreeBaseCode, genCount]

@[simp] theorem zeroBaseInput_innerLayers :
    innerCompilerLayers zeroBaseInput = [[], []] := rfl

/-- Two empty edge layers have exact identity subgroup semantics. -/
noncomputable def twoEmptyExactLayers (c : PresentationCode) :
    ExactChain c [[], []] :=
  (singletonCentral c []).append
    (singletonCentral (edgeCode c []) [])

/-- The genuine inner exactness obligation for the zero-base input is closed. -/
noncomputable def zeroBaseExactChain :
    ExactChain zeroBaseInput.1 (innerCompilerLayers zeroBaseInput) :=
  twoEmptyExactLayers rankThreeBaseCode

/-- The emitted finite presentation and its three literal marked words. -/
def zeroBaseMarkedOutput : Output := compileMarked zeroBaseInput

/-- Producing the concrete zero-base tower input is primitive recursive. -/
theorem primrec_zeroBaseInput : Primrec (fun _ : Unit => zeroBaseInput) :=
  Primrec.const _

/-- Producing its marked finite-presentation output is primitive recursive. -/
theorem primrec_zeroBaseMarkedOutput :
    Primrec (fun _ : Unit => zeroBaseMarkedOutput) :=
  primrec_compileMarked.comp primrec_zeroBaseInput

/-- Each literal output mark evaluates to the image of the corresponding
free rank-three generator under the closed compiler embedding. -/
theorem zeroBaseEmbedding_eq_mark (i : Fin 3) :
    compilerEmbedding zeroBaseInput zeroBaseExactChain
        (PresentedGroup.of (baseIndex zeroBaseInput (by decide) i)) =
      compiledWord zeroBaseInput (rankThreeWord i) :=
  compilerEmbedding_eq_rankThreeWord zeroBaseInput zeroBaseExactChain
    (by decide) i

/-- The free rank-three base embeds in the emitted zero-base presentation. -/
theorem zeroBaseEmbedding_injective :
    Function.Injective
      (compilerEmbedding zeroBaseInput zeroBaseExactChain) :=
  compilerEmbedding_injective zeroBaseInput zeroBaseExactChain

/-! ## Higman's successor base -/

/-- Raw commutator spelling `x y x⁻¹ y⁻¹`. -/
def commutatorWord (x y : ℕ) : FreeEdgeTowerCode.Raw :=
  [(x, true), (y, true), (x, false), (y, false)]

/-- The six relators of the flip-group presentation
`⟨a,b,c,β,γ | [β,b],[β,c],[γ,b],[γ,c],[a,bβ],[a,cγ]⟩`. -/
def successorBaseRelators : List FreeEdgeTowerCode.Raw :=
  [commutatorWord 3 1, commutatorWord 3 2,
    commutatorWord 4 1, commutatorWord 4 2,
    [(0, true), (1, true), (3, true), (0, false), (3, false), (1, false)],
    [(0, true), (2, true), (4, true), (0, false), (4, false), (2, false)]]

/-- Literal finite presentation of the two-stage flip group `G₂`.  The code
stores the maximum generator index, hence `4` denotes five generators. -/
def successorBaseCode : PresentationCode := (4, successorBaseRelators)

/-- In the displayed `G₂` alphabet, this spells
`a_(0,1) = (c⁻¹bc)⁻¹ a (c⁻¹bc)`. -/
def successorOrbitWord : FreeEdgeTowerCode.Raw :=
  [(2, false), (1, false), (2, true), (0, true),
    (2, false), (1, true), (2, true)]

/-- In the displayed `G₂` alphabet, this spells the two-sided translation
`s = β (c⁻¹bc)⁻¹`. -/
def successorShiftWord : FreeEdgeTowerCode.Raw :=
  [(3, true), (2, false), (1, false), (2, true)]

/-- **Concrete successor-base tower input.**  Its detector centralizes the
two displayed generators of Higman's cutting subgroup for `S`. -/
def successorBaseInput : TowerInput :=
  (successorBaseCode,
    ([], ([], ([], [successorOrbitWord, successorShiftWord]))))

@[simp] theorem successorBaseInput_genCount :
    genCount successorBaseInput.1 = 5 := by
  simp [successorBaseInput, successorBaseCode, genCount]

@[simp] theorem successorBaseInput_innerLayers :
    innerCompilerLayers successorBaseInput = [[], []] := rfl

/-- The successor gadget's two compulsory inner slots are exact identity
edges; its nontrivial semantic payload is entirely in the final detector. -/
noncomputable def successorBaseExactChain :
    ExactChain successorBaseInput.1 (innerCompilerLayers successorBaseInput) :=
  twoEmptyExactLayers successorBaseCode

/-- The marked finite-presentation output of the successor gadget. -/
def successorBaseMarkedOutput : Output := compileMarked successorBaseInput

theorem primrec_successorBaseInput :
    Primrec (fun _ : Unit => successorBaseInput) := Primrec.const _

theorem primrec_successorBaseMarkedOutput :
    Primrec (fun _ : Unit => successorBaseMarkedOutput) :=
  primrec_compileMarked.comp primrec_successorBaseInput

/-- The presented flip-group base embeds in the emitted successor-base
detector presentation. -/
theorem successorBaseEmbedding_injective :
    Function.Injective
      (compilerEmbedding successorBaseInput successorBaseExactChain) :=
  compilerEmbedding_injective successorBaseInput successorBaseExactChain

/-- The first three literal output marks still carry `a,b,c`. -/
theorem successorBaseEmbedding_eq_mark (i : Fin 3) :
    compilerEmbedding successorBaseInput successorBaseExactChain
        (PresentedGroup.of (baseIndex successorBaseInput (by decide) i)) =
      compiledWord successorBaseInput (rankThreeWord i) :=
  compilerEmbedding_eq_rankThreeWord successorBaseInput successorBaseExactChain
    (by decide) i

/-! ## Executable dispatch for the two Higman atoms -/

/-- Reified atomic Higman program: `false` is `Z`, `true` is `S`.  Using
`Bool` keeps the compiler input in an existing `Primcodable` type. -/
def baseInput : Bool → TowerInput
  | false => zeroBaseInput
  | true => successorBaseInput

/-- The atomic compiler carries a closed exact chain in either branch. -/
noncomputable def baseExactChain : (b : Bool) →
    ExactChain (baseInput b).1 (innerCompilerLayers (baseInput b))
  | false => zeroBaseExactChain
  | true => successorBaseExactChain

/-- Compile either reified Higman atom to a marked finite presentation. -/
def compileBaseMarked (b : Bool) : Output := compileMarked (baseInput b)

theorem primrec_baseInput : Primrec baseInput :=
  (Primrec.cond Primrec.id (Primrec.const successorBaseInput)
    (Primrec.const zeroBaseInput)).of_eq fun b => by cases b <;> rfl

theorem primrec_compileBaseMarked : Primrec compileBaseMarked :=
  primrec_compileMarked.comp primrec_baseInput

theorem baseEmbedding_injective (b : Bool) :
    Function.Injective (compilerEmbedding (baseInput b) (baseExactChain b)) :=
  compilerEmbedding_injective (baseInput b) (baseExactChain b)

end ReifiedPrimrecTower
end Higman
end GroupApproximation
