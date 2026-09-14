import Mathlib.Computability.TuringDegree
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import GroupApproximation.Dynamics.SubshiftWordGraph
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Setting
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianSubshift

/-!
# Statements for the section "Word problems and factors" of `simple_kazhdan_sofic_group.tex`

The note at the origin tip 696c4b602, corollary `cor:wp`:

> The word problem of `G_X` has the Turing degree of the language `L(X)` of `X`. In particular
> `G_X` has solvable word problem if and only if `L(X)` is recursive, as for the Fibonacci subshift
> `X_{(3-√5)/2}` below. Every Turing degree occurs, and there are continuum many groups `G_X`, none
> of which is isomorphic to a subgroup of another.

The objects `subshiftHomeo`, `IsMinimal`, `letterIndicator`, `R` and `G` come from the shared
`Setting` module, and `sturmianSubshift` from `SturmianSubshift`. This module adds:

* `language S`: the language `L(X)` as finite lists, through `WordGraph.language`;
* `genValue S`: the generators `e_ij(s)` for `s ∈ {u, u⁻¹} ∪ {e_a : a ∈ A}` (section "The ring and
  property (T)");
* `wordProblemOracle`, `languageOracle`, `charOracle` and `slopeOracle`: the characteristic functions
  whose Turing degrees the section compares, as partial functions `ℕ →. ℕ` for Mathlib's
  `TuringReducible`, over `Primcodable` codes;
* the printed propositions, as named `Prop`s.

"Every Turing degree" is spelled over sets of naturals, which the proof represents by continued
fractions. The proofs are built in separate modules.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift Set

/-- The language `L(X)`, as finite lists of letters, through `WordGraph.language`. -/
def language {A : Type} [TopologicalSpace A] (S : Subshift A ℤ) : Set (List A) :=
  {v | (fun j : Fin v.length => v.get j) ∈ WordGraph.language S.carrier v.length}

/-- The coefficient symbols `{u, u⁻¹} ∪ {e_a : a ∈ A}` of the generators. -/
inductive Coeff (A : Type) where
  | u
  | uInv
  | letter (a : A)

/-- `Coeff A` as a nested option, for the encoding of words. -/
def Coeff.equivOption (A : Type) : Coeff A ≃ Option (Option A) where
  toFun
    | .u => none
    | .uInv => some none
    | .letter a => some (some a)
  invFun
    | none => .u
    | some none => .uInv
    | some (some a) => .letter a
  left_inv c := by cases c <;> rfl
  right_inv o := by
    match o with
    | none => rfl
    | some none => rfl
    | some (some _) => rfl

instance (A : Type) [Primcodable A] : Primcodable (Coeff A) :=
  Primcodable.ofEquiv _ (Coeff.equivOption A)

/-- The off-diagonal positions of `M₃`. -/
abbrev OffDiag : Type := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

instance : Primcodable OffDiag :=
  Primcodable.subtype
    (PrimrecPred.of_eq ((PrimrecRel.not Primrec.eq).comp Primrec.fst Primrec.snd) fun _ => Iff.rfl)

/-- The generator symbols: an off-diagonal position and a coefficient symbol. -/
abbrev Gen (A : Type) : Type := OffDiag × Coeff A

section Group

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A]

/-- The value of a coefficient symbol in `R`. -/
noncomputable def coeffValue (S : Subshift A ℤ) : Coeff A → R S
  | .u => (ClopenCrossedProduct.unit (subshiftHomeo S) (ZMod 2) : R S)
  | .uInv => ((ClopenCrossedProduct.unit (subshiftHomeo S) (ZMod 2))⁻¹ : (R S)ˣ)
  | .letter a => ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (letterIndicator S a)

/-- The generators `e_ij(s)` of `G_X`. -/
noncomputable def genValue (S : Subshift A ℤ) (g : Gen A) : G S :=
  ⟨elementaryUnit g.1.1.1 g.1.1.2 g.1.2 (coeffValue S g.2), elementaryUnit_mem _ _ _ _⟩

end Group

section Oracles

/-- The value of a word `w` in the generators `s`; a letter `(i, false)` stands for `(s i)⁻¹`. -/
def wordValue {ι H : Type*} [Group H] (s : ι → H) : List (ι × Bool) → H
  | [] => 1
  | (i, b) :: w => (if b then s i else (s i)⁻¹) * wordValue s w

open Classical in
/-- The characteristic function of the word problem in the generators `s`, on codes of words. -/
noncomputable def wordProblemOracle {ι H : Type*} [Group H] [Primcodable ι] (s : ι → H) :
    ℕ →. ℕ :=
  fun n => Part.some
    (if ∃ w : List (ι × Bool), Encodable.decode n = some w ∧ wordValue s w = 1 then 1 else 0)

open Classical in
/-- The characteristic function of a set of naturals. -/
noncomputable def charOracle (B : Set ℕ) : ℕ →. ℕ :=
  fun n => Part.some (if n ∈ B then 1 else 0)

open Classical in
/-- The characteristic function of the language `L(X)`, on codes of words. -/
noncomputable def languageOracle {A : Type} [TopologicalSpace A] [Primcodable A]
    (S : Subshift A ℤ) : ℕ →. ℕ :=
  fun n => Part.some
    (if ∃ v : List A, Encodable.decode n = some v ∧ v ∈ language S then 1 else 0)

open Classical in
/-- The strict cut `a < b α` of `α` on codes `n = Nat.pair a b`: the oracle through which a real
`α > 0` computes and is computed. -/
noncomputable def slopeOracle (α : ℝ) : ℕ →. ℕ :=
  fun n => Part.some (if ((Nat.unpair n).1 : ℝ) < ((Nat.unpair n).2 : ℝ) * α then 1 else 0)

/-- `α = [0; a_0, a_1, …]`: the continued fraction expansion of `α` has integer part `0` and
partial denominators `a`. -/
def IsContinuedFractionOf (α : ℝ) (a : ℕ → ℕ) : Prop :=
  (GenContFract.of α).h = 0 ∧ ∀ k : ℕ, (GenContFract.of α).partDens.get? k = some (a k : ℝ)

end Oracles

/-- **Proof, first paragraph.**  Multiplying out a word gives coefficient tables; the word is
trivial in `G_X` if and only if the tables of its difference from `I_3` vanish on `L(X)`; so `L(X)`
computes the word problem. -/
def PrintedWordProblemReducesToLanguage : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
    [Primcodable A] (S : Subshift A ℤ),
      TuringReducible (wordProblemOracle (genValue S)) (languageOracle S)

/-- **Proof, first paragraph.**  A word for `e_12(∏_{t<m} u^{-t} e_{v_t} u^t)` is computable from
`v`, and it is trivial if and only if `v ∉ L(X)`; so the word problem computes `L(X)`. -/
def PrintedLanguageReducesToWordProblem : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
    [Primcodable A] (S : Subshift A ℤ),
      TuringReducible (languageOracle S) (wordProblemOracle (genValue S))

/-- **`cor:wp`, first sentence.**  The word problem of `G_X` has the Turing degree of `L(X)`. -/
def PrintedWordProblemDegreeEqLanguage : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
    [Primcodable A] (S : Subshift A ℤ), Infinite S.carrier → IsMinimal S →
      TuringEquivalent (wordProblemOracle (genValue S)) (languageOracle S)

/-- **`cor:wp`, second sentence.**  `G_X` has solvable word problem if and only if `L(X)` is
recursive. -/
def PrintedSolvableWordProblemIffRecursiveLanguage : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
    [Primcodable A] (S : Subshift A ℤ), Infinite S.carrier → IsMinimal S →
      (Partrec (wordProblemOracle (genValue S)) ↔ Partrec (languageOracle S))

/-- **`cor:wp`, second sentence, "as for the Fibonacci subshift `X_{(3-√5)/2}`".**  Its group has
solvable word problem. -/
def PrintedFibonacciSolvableWordProblem : Prop :=
  Partrec (wordProblemOracle (genValue (sturmianSubshift ((3 - Real.sqrt 5) / 2))))

open Classical in
/-- **Proof, second paragraph.**  Every set `S ⊆ ℕ` has the degree of the irrational number
`[0; 1 + χ_S(0), 1 + χ_S(1), …]`. -/
def PrintedContinuedFractionRepresentative : Prop :=
  ∀ B : Set ℕ, ∃ α : ℝ, IsContinuedFractionOf α (fun k => 1 + if k ∈ B then 1 else 0) ∧
    Irrational α ∧ TuringEquivalent (slopeOracle α) (charOracle B)

/-- **Proof, second paragraph.**  If a finitely generated group `H` embeds in a finitely generated
group `G`, a word for `H` becomes a word for `G` by substituting for its generators, so the word
problem of `H` reduces to that of `G`. -/
def PrintedWordProblemReducesUnderEmbedding : Prop :=
  ∀ (H G : Type) [Group H] [Group G] (ι κ : Type) [Primcodable ι] [Primcodable κ] [Finite ι]
    [Finite κ] (s : ι → G) (t : κ → H) (ψ : H →* G), Function.Injective ψ →
      Subgroup.closure (range s) = ⊤ → Subgroup.closure (range t) = ⊤ →
        TuringReducible (wordProblemOracle t) (wordProblemOracle s)

/-- **Proof, second paragraph.**  The Turing degrees contain an antichain of size continuum. -/
def PrintedTuringAntichainContinuum : Prop :=
  ∃ F : Set (Set ℕ), Cardinal.mk F = Cardinal.continuum ∧
    ∀ B ∈ F, ∀ C ∈ F, TuringReducible (charOracle B) (charOracle C) → B = C

/-- **Corollary `cor:wp`.**  The word problem of `G_X` has the Turing degree of `L(X)`; `G_X` has
solvable word problem if and only if `L(X)` is recursive, as for the Fibonacci subshift; every
Turing degree occurs; and there are continuum many groups `G_X`, none of which is isomorphic to a
subgroup of another. -/
def PrintedWordProblemsCorollary : Prop :=
  PrintedWordProblemDegreeEqLanguage ∧ PrintedSolvableWordProblemIffRecursiveLanguage ∧
    PrintedFibonacciSolvableWordProblem ∧
    (∀ B : Set ℕ, ∃ S : Subshift Bool ℤ, Infinite S.carrier ∧ IsMinimal S ∧
      TuringEquivalent (wordProblemOracle (genValue S)) (charOracle B)) ∧
    ∃ F : Set (Subshift Bool ℤ), Cardinal.mk F = Cardinal.continuum ∧
      (∀ S ∈ F, Infinite S.carrier ∧ IsMinimal S) ∧
      ∀ S ∈ F, ∀ S' ∈ F, (∃ ψ : G S →* G S', Function.Injective ψ) → S = S'

end SimpleKazhdanSofic
end GroupApproximation
