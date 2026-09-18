import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralCertificate.Semantics
import GroupApproximation.Manuscript.NonMFNotes.Full.RadicalArithmetic.Arithmetic
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-radical-arithmetic`: the `Π⁰₂` / `Σ⁰₂` classification through `D(P,v,n,d)`

Manuscript `non_mf_group_notes.tex`, `thm:mf-radical-arithmetic`:

> "Uniformly in a finite presentation `P` and a word `v`,
> `v ∉ Res_MF(G_P)` is `Π⁰₂` and `v ∈ Res_MF(G_P)` is `Σ⁰₂`.  The same `Σ⁰₂`
> upper bound holds for the set of radical words after fixing `P`."
>
> Proof: "... `v ∉ Res_MF(G_P) ⟺ ∀ n ∃ d D(P,v,n,d)`, and complementation
> proves the claim."

The predicates classified here are the literal manuscript shapes
`∀ n ∃ d D(P,v,n,d)` (`LiteralNonRadical`) and its complement
`∃ n ∀ d ¬ D(P,v,n,d)` (`LiteralRadical`).  Both are identified with NN02's
radical-word predicate `NN02.RadicalWordCode` via
`manuscriptLiteralRadicalWordSemantics`, and NN02's primitive-recursive
matrix-answer checker supplies the r.e. inner matrix of the `Π⁰₂` form.
-/

namespace GroupApproximation.Full.NN02b

open ArithmeticalHierarchy PresentationCodes AdianRabinWordProblem MFMicrostate

noncomputable section

/-- The printed non-membership form `∀ n ∃ d D(P,v,n,d)`. -/
def LiteralNonRadical (p : PresentationCode × List (ℕ × Bool)) : Prop :=
  ∀ n, ∃ d, LiteralD p.1 p.2 n d

/-- Its complement, the membership form `∃ n ∀ d ¬ D(P,v,n,d)`. -/
def LiteralRadical (p : PresentationCode × List (ℕ × Bool)) : Prop :=
  ∃ n, ∀ d, ¬ LiteralD p.1 p.2 n d

theorem not_literalRadical_iff (p : PresentationCode × List (ℕ × Bool)) :
    ¬ LiteralRadical p ↔ LiteralNonRadical p := by
  constructor
  · intro h n
    by_contra hn
    exact h ⟨n, fun d hd => hn ⟨d, hd⟩⟩
  · rintro h ⟨n, hn⟩
    obtain ⟨d, hd⟩ := h n
    exact hn d hd

/-- `¬ (v ∈ Res_MF(G_P)) ⟺ ∀ n ∃ d D(P,v,n,d)`. -/
theorem not_radicalWordCode_iff_literalNonRadical (p : PresentationCode × List (ℕ × Bool)) :
    ¬ NN02.RadicalWordCode p ↔ LiteralNonRadical p :=
  not_mem_manuscriptCoronaMFResidual_iff_literalD p.1 p.2

/-- `v ∈ Res_MF(G_P) ⟺ ∃ n ∀ d ¬ D(P,v,n,d)`. -/
theorem literalRadical_iff_radicalWordCode (p : PresentationCode × List (ℕ × Bool)) :
    LiteralRadical p ↔ NN02.RadicalWordCode p := by
  constructor
  · intro h
    by_contra hc
    exact (not_literalRadical_iff p).2 ((not_radicalWordCode_iff_literalNonRadical p).1 hc) h
  · intro h
    by_contra hc
    exact (not_radicalWordCode_iff_literalNonRadical p).2 ((not_literalRadical_iff p).1 hc) h

/-- **`thm:mf-radical-arithmetic`, first clause, literal form**
(`non_mf_group_notes.tex`): `∀ n ∃ d D(P,v,n,d)`, i.e. `v ∉ Res_MF(G_P)`, is
`Π⁰₂` uniformly in `P` and `v`. -/
theorem literalNonRadical_pi02 : Pi02 LiteralNonRadical :=
  (pi02_congr not_radicalWordCode_iff_literalNonRadical).1 NN02.nonRadicalWord_pi02

/-- **`thm:mf-radical-arithmetic`, second clause, literal form**
(`non_mf_group_notes.tex`): `∃ n ∀ d ¬ D(P,v,n,d)`, i.e. `v ∈ Res_MF(G_P)`, is
`Σ⁰₂` uniformly in `P` and `v` (complementation). -/
theorem literalRadical_sigma02 : Sigma02 LiteralRadical :=
  (pi02_congr fun p => (not_literalRadical_iff p).symm).1 literalNonRadical_pi02

/-- The fixed-presentation clause for the literal membership form. -/
def LiteralFixedPresentationRadicalSigma02 : Prop :=
  ∀ c : PresentationCode, Sigma02 fun v : List (ℕ × Bool) => LiteralRadical (c, v)

/-- **`thm:mf-radical-arithmetic`, third clause, literal form**
(`non_mf_group_notes.tex`): after fixing `P`, `{v : ∃ n ∀ d ¬ D(P,v,n,d)}` is
`Σ⁰₂`. -/
theorem literalFixedPresentation_radical_sigma02 : LiteralFixedPresentationRadicalSigma02 :=
  fun c => (sigma02_congr fun v => (literalRadical_iff_radicalWordCode (c, v)).symm).1
    (NN02.fixedPresentation_radicalWord_sigma02 c)

/-- All three clauses of `thm:mf-radical-arithmetic`, stated through the literal
predicate `D(P,v,n,d)`, together with the printed equivalence. -/
def LiteralMFRadicalArithmetic : Prop :=
  LiteralRadicalWordSemantics ∧ Pi02 LiteralNonRadical ∧ Sigma02 LiteralRadical ∧
    LiteralFixedPresentationRadicalSigma02

/-- **`thm:mf-radical-arithmetic`** (`non_mf_group_notes.tex`), through the
literal predicate `D(P,v,n,d)`, closed. -/
theorem manuscriptLiteralMFRadicalArithmetic : LiteralMFRadicalArithmetic :=
  ⟨manuscriptLiteralRadicalWordSemantics, literalNonRadical_pi02, literalRadical_sigma02,
    literalFixedPresentation_radical_sigma02⟩

end

#audit_closed_axioms GroupApproximation.Full.NN02b.literalNonRadical_pi02
#audit_closed_axioms GroupApproximation.Full.NN02b.literalRadical_sigma02
#audit_closed_axioms GroupApproximation.Full.NN02b.literalFixedPresentation_radical_sigma02
#audit_closed_axioms GroupApproximation.Full.NN02b.manuscriptLiteralMFRadicalArithmetic

end GroupApproximation.Full.NN02b
