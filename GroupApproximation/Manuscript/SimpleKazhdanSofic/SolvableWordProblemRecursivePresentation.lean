import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSolvableWordProblem
import GroupApproximation.Higman.Program
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Computability.RE
import Mathlib.Computability.Primrec.List

/-!
# A group with solvable word problem is recursively presented

This supports the instances in the last statement of `cor:host` in `simple_kazhdan_sofic_group.tex` at
origin/main 696c4b602 (tex l.324–327):

> So one such group contains every recursively presented finitely generated LEF group, for instance
> every finitely presented residually finite group and every `G_Y` whose language is recursive.

A group `G_Y` whose language is recursive has solvable word problem. This file proves that solvable
word problem, in the form `HasSolvableWordProblem`, gives a `Higman.RecursivePresentation`.

* `natGen s`: the generating family `s : ι → Γ` re-indexed by `ℕ`. A code of `i` names `s i`, and
  every other number names `1`.
* `rawToFamily`: a raw word as a word in `s`, dropping the letters that name no generator.
* `evalRaw_natGen`: the two evaluations agree.
* `nonempty_recursivePresentation_of_hasSolvableWordProblem`: triviality of raw words is decided
  by the computable word problem of `s`, so it is recursively enumerable.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open Encodable

section Transfer

variable {Γ : Type} [Group Γ] {ι : Type} [Primcodable ι]

/-- The generating family `s` indexed by `ℕ`: codes of `i` name `s i`, other numbers name `1`. -/
def natGen (s : ι → Γ) (k : ℕ) : Γ :=
  (decode (α := ι) k).elim 1 s

/-- A letter as a word in the family: dropped if its index names no generator. -/
def letterToFamily (p : ℕ × Bool) : List (ι × Bool) :=
  (decode (α := ι) p.1).elim [] fun i => [(i, p.2)]

/-- A raw word as a word in the family. -/
def rawToFamily (w : Higman.RawWord) : List (ι × Bool) :=
  w.flatMap (letterToFamily (ι := ι))

theorem evalRaw_natGen (s : ι → Γ) (w : Higman.RawWord) :
    Higman.evalRaw (natGen s) w = wordValue s (rawToFamily (ι := ι) w) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    obtain ⟨k, b⟩ := p
    rw [Higman.evalRaw_cons, ih]
    cases h : decode (α := ι) k with
    | none =>
      simp [natGen, rawToFamily, letterToFamily, h]
    | some i =>
      simp [natGen, rawToFamily, letterToFamily, h, wordValue_cons]

theorem closure_range_natGen {s : ι → Γ} (hs : Subgroup.closure (Set.range s) = ⊤) :
    Subgroup.closure (Set.range (natGen s)) = ⊤ := by
  rw [eq_top_iff, ← hs]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨encode i, by simp [natGen, Encodable.encodek]⟩

theorem primrec_letterToFamily : Primrec (letterToFamily (ι := ι)) := by
  have hg : Primrec₂ fun (p : ℕ × Bool) (i : ι) => [(i, p.2)] :=
    (Primrec.list_cons.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.const [])).to₂
  refine Primrec.of_eq
    (Primrec.option_casesOn (Primrec.decode.comp Primrec.fst) (Primrec.const []) hg) ?_
  intro p
  unfold letterToFamily
  cases decode (α := ι) p.1 <;> rfl

theorem primrec_rawToFamily : Primrec (rawToFamily (ι := ι)) :=
  Primrec.list_flatMap Primrec.id (primrec_letterToFamily.comp Primrec.snd).to₂

/-- **Solvable word problem gives a recursive presentation.** -/
theorem nonempty_recursivePresentation_of_hasSolvableWordProblem
    (h : HasSolvableWordProblem Γ) : Nonempty (Higman.RecursivePresentation Γ) := by
  classical
  obtain ⟨ι, _, _, s, hs, hpart⟩ := h
  let o : ℕ → ℕ := fun n => (wordProblemOracle s n).get trivial
  have ho : Computable o := Partrec.of_eq hpart fun _ => rfl
  have hval : ∀ v : List (ι × Bool), o (encode v) = 1 ↔ wordValue s v = 1 := by
    intro v
    simp [o, wordProblemOracle, Encodable.encodek]
  have hc : Computable fun w : Higman.RawWord => o (encode (rawToFamily (ι := ι) w)) :=
    ho.comp (Primrec.encode.comp primrec_rawToFamily).to_comp
  obtain ⟨inst, hprim⟩ := (Primrec.eq : PrimrecRel (@Eq ℕ))
  have hdec : Computable fun w : Higman.RawWord =>
      @decide ((o (encode (rawToFamily (ι := ι) w)), 1).1 = (o (encode (rawToFamily (ι := ι) w)), 1).2)
        (inst (o (encode (rawToFamily (ι := ι) w)), 1)) :=
    hprim.to_comp.comp (Computable.pair hc (Computable.const 1))
  have hp : ComputablePred fun w : Higman.RawWord => o (encode (rawToFamily (ι := ι) w)) = 1 :=
    ⟨inferInstance, Computable.of_eq hdec fun _ => decide_eq_decide.mpr Iff.rfl⟩
  have hre : REPred fun w : Higman.RawWord => Higman.evalRaw (natGen s) w = 1 :=
    (hp.of_eq fun w => by rw [hval, evalRaw_natGen]).to_re
  exact ⟨{ gen := natGen s, spans := closure_range_natGen hs, re := hre }⟩

end Transfer

#audit_axioms GroupApproximation.SimpleKazhdanSofic.evalRaw_natGen
#audit_axioms GroupApproximation.SimpleKazhdanSofic.nonempty_recursivePresentation_of_hasSolvableWordProblem

end SimpleKazhdanSofic
end GroupApproximation
