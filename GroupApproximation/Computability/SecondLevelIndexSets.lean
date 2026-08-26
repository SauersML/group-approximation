import GroupApproximation.Computability.ArithmeticalHierarchy
import GroupApproximation.Computability.WordProblemRE
import Mathlib.Data.Set.Finite.Basic

/-!
# Canonical second-level index sets

For a partial-recursive program code, infinitude of its domain is the canonical
`Π⁰₂` question and finiteness is its `Σ⁰₂` complement.  This file starts from
the step-indexed evaluator, so every search predicate below has a concrete
computable Boolean matrix.
-/

namespace GroupApproximation
namespace SecondLevelIndexSets

open ArithmeticalHierarchy
open Nat.Partrec

/-- The domain of a partial-recursive program code. -/
def codeDomain (c : Code) : Set ℕ :=
  {n | (Code.eval c n).Dom}

/-- The canonical `Π⁰₂` index set. -/
def InfiniteDomain (c : Code) : Prop :=
  (codeDomain c).Infinite

/-- Its complementary `Σ⁰₂` index set. -/
def FiniteDomain (c : Code) : Prop :=
  (codeDomain c).Finite

/-- A bounded evaluator witness: an input strictly above the requested bound
halts by the displayed evaluation stage. -/
def aboveCheck (cn : Code × ℕ) (witness : ℕ × ℕ) : Bool :=
  decide (cn.2 < witness.1) &&
    (Code.evaln witness.2 cn.1 witness.1).isSome

theorem primrec_aboveCheck : Primrec₂ aboveCheck := by
  have hcode : Primrec fun z : (Code × ℕ) × (ℕ × ℕ) => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hbound : Primrec fun z : (Code × ℕ) × (ℕ × ℕ) => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hinput : Primrec fun z : (Code × ℕ) × (ℕ × ℕ) => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hstage : Primrec fun z : (Code × ℕ) × (ℕ × ℕ) => z.2.2 :=
    Primrec.snd.comp Primrec.snd
  have heval : Primrec fun z : (Code × ℕ) × (ℕ × ℕ) =>
      Code.evaln z.2.2 z.1.1 z.2.1 :=
    Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair hstage hcode) hinput)
  exact (Primrec.and.comp
    (Primrec.nat_lt.comp hbound hinput).decide
    (Primrec.option_isSome.comp heval)).of_eq fun _ => rfl

theorem computable_aboveCheck : Computable₂ aboveCheck :=
  primrec_aboveCheck.to_comp

/-- Halting is witnessed at some finite evaluator stage. -/
theorem eval_dom_iff_exists_evaln_isSome (c : Code) (n : ℕ) :
    (Code.eval c n).Dom ↔ ∃ stage, (Code.evaln stage c n).isSome := by
  constructor
  · intro h
    rw [Part.dom_iff_mem] at h
    obtain ⟨x, hx⟩ := h
    obtain ⟨stage, hstage⟩ := Code.evaln_complete.mp hx
    exact ⟨stage, Option.isSome_iff_exists.mpr ⟨x, hstage⟩⟩
  · rintro ⟨stage, hstage⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hstage
    rw [Part.dom_iff_mem]
    exact ⟨x, Code.evaln_sound hx⟩

/-- The Boolean search matrix says exactly that the program domain has a
member above the requested bound. -/
theorem exists_aboveCheck_iff (c : Code) (bound : ℕ) :
    (∃ witness, aboveCheck (c, bound) witness = true) ↔
      ∃ n, bound < n ∧ (Code.eval c n).Dom := by
  constructor
  · rintro ⟨⟨n, stage⟩, h⟩
    simp only [aboveCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨n, h.1, (eval_dom_iff_exists_evaln_isSome c n).2 ⟨stage, h.2⟩⟩
  · rintro ⟨n, hbn, hn⟩
    obtain ⟨stage, hstage⟩ := (eval_dom_iff_exists_evaln_isSome c n).1 hn
    exact ⟨(n, stage), by simp [aboveCheck, hbn, hstage]⟩

/-- Uniform recursive enumerability of the unbounded-domain challenge. -/
theorem rePred_hasDomainAbove :
    REPred fun cn : Code × ℕ =>
      ∃ n, cn.2 < n ∧ (Code.eval cn.1 n).Dom := by
  refine (WordProblemRE.rePred_exists_eq_true computable_aboveCheck).of_eq ?_
  intro cn
  exact exists_aboveCheck_iff cn.1 cn.2

/-- Infinitude of a program domain is a `Π⁰₂` predicate. -/
theorem infiniteDomain_pi02 : Pi02 InfiniteDomain := by
  refine pi02_of_re_family rePred_hasDomainAbove ?_
  intro c
  simpa only [InfiniteDomain, codeDomain, Set.mem_setOf_eq, and_comm] using
    (Set.infinite_iff_exists_gt (s := codeDomain c))

/-- Finiteness of a program domain is a `Σ⁰₂` predicate. -/
theorem finiteDomain_sigma02 : Sigma02 FiniteDomain := by
  refine (sigma02_congr fun c => ?_).2
    ((sigma02_compl_iff InfiniteDomain).2 infiniteDomain_pi02)
  classical
  simp only [FiniteDomain, InfiniteDomain, Set.Infinite, not_not]

end SecondLevelIndexSets
end GroupApproximation
