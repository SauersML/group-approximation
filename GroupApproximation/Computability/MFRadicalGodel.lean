import GroupApproximation.Computability.MFRadicalComputer
import Mathlib.Computability.PartrecCode

/-!
# Gödel incompleteness inside the fixed MF-radical computer

This file internalizes the proof-search and Kleene-recursion layer missing from
`MFRadicalComputer`.  A computably axiomatized proof system is represented by
a partial-recursive semidecision procedure on formula codes.  The code `c`
names the concrete formula

    `MFRadicalComputer.codeWord c ≠ 1`.

Restricted soundness means only that whenever the semidecision procedure
halts on `c`, this particular group-theoretic formula is true.  No soundness
for any other language or formula is assumed.

Mathlib's `Nat.Partrec.Code.fixed_point₂` supplies a code whose execution is
the proof search for the formula bearing that same code.  If the search
halted, universal correctness of the radical computer would make the word
trivial, contradicting restricted soundness.  Hence it does not halt; the word
is therefore nontrivial, remains MF-invisible, and is not proved.
-/

namespace GroupApproximation
namespace MFRadicalGodel

open Nat.Partrec (Code)
open Nat.Partrec.Code
open MFRadicalComputer

noncomputable section

/-- A computably enumerable proof system for the formulas indexed by partial
recursive codes.  `search c` terminates exactly when the system proves the
formula bearing code `c`; its returned `PUnit` contains no semantic data. -/
structure ProofSystem where
  search : Code →. PUnit
  search_partrec : Partrec search

namespace ProofSystem

/-- The provability predicate presented by the proof-search procedure. -/
def Proves (T : ProofSystem) (c : Code) : Prop := (T.search c).Dom

/-- Provability in a `ProofSystem` is recursively enumerable by construction. -/
theorem proves_re (T : ProofSystem) : REPred T.Proves :=
  T.search_partrec.dom_re

/-- Restricted soundness for the only formulas used in the diagonal: proofs
of `c` certify that the corresponding word in the fixed radical computer is
nontrivial. -/
def Sound (T : ProofSystem) : Prop :=
  ∀ c : Code, T.Proves c → codeWord c ≠ 1

end ProofSystem

/-- Given a candidate self-code `c`, search for a proof of the formula bearing
that code and halt with `0` when the proof search succeeds.  The ordinary
program input is intentionally ignored. -/
def diagonalSearch (T : ProofSystem) (c : Code) (_ : ℕ) : Part ℕ :=
  (T.search c).map fun _ => 0

/-- The diagonal proof-search family is partial recursive uniformly in its
candidate self-code. -/
theorem diagonalSearch_partrec₂ (T : ProofSystem) :
    Partrec₂ (diagonalSearch T) := by
  have hpair : Partrec fun p : Code × ℕ =>
      (T.search p.1).map fun _ => 0 :=
    (T.search_partrec.comp Computable.fst).map (Computable.const 0).to₂
  exact hpair.to₂

/-- The diagonal program halts exactly when the theory proves the formula
indexed by its candidate self-code. -/
theorem diagonalSearch_dom_iff (T : ProofSystem) (c : Code) (n : ℕ) :
    (diagonalSearch T c n).Dom ↔ T.Proves c := by
  simp [diagonalSearch, ProofSystem.Proves]

/-- Kleene's second recursion theorem, specialized to proof search for the
fixed radical-computer word named by the program's own code. -/
theorem exists_proofSearch_fixedPoint (T : ProofSystem) :
    ∃ c : Code, eval c = diagonalSearch T c :=
  fixed_point₂ (diagonalSearch_partrec₂ T)

/-- **Gödel incompleteness in the fixed MF radical.**  Every computably
axiomatized proof system sound for the concrete statements
`codeWord c ≠ 1` misses one true such statement.  The missed word belongs to
the MF residual and even to its commutator layer. -/
theorem exists_true_unprovable_radical_word (T : ProofSystem)
    (hsound : T.Sound) :
    ∃ c : Code,
      codeWord c ≠ 1 ∧
        NormMFInvisible (codeWord c) ∧
        codeWord c ∈ ⁅normMFResidual MFRadicalComputer.Carrier,
          (⊤ : Subgroup MFRadicalComputer.Carrier)⁆ ∧
        ¬ T.Proves c := by
  obtain ⟨c, hfix⟩ := exists_proofSearch_fixedPoint T
  have hnotProves : ¬ T.Proves c := by
    intro hproves
    have hdom : (eval c 0).Dom := by
      rw [hfix]
      exact (diagonalSearch_dom_iff T c 0).2 hproves
    exact (hsound c hproves) ((codeWord_eq_one_iff_eval_dom c).2 hdom)
  have hnotDom : ¬ (eval c 0).Dom := by
    intro hdom
    have hdiag : (diagonalSearch T c 0).Dom := by
      rw [← hfix]
      exact hdom
    exact hnotProves ((diagonalSearch_dom_iff T c 0).1 hdiag)
  have hnontrivial : codeWord c ≠ 1 := by
    intro hone
    exact hnotDom ((codeWord_eq_one_iff_eval_dom c).1 hone)
  exact ⟨c, hnontrivial, codeWord_normMFInvisible c,
    codeWord_mem_commutator_residual c, hnotProves⟩

/-- Closed endpoint, exposing the fixed finitely presented carrier together
with the theory-relative incompleteness theorem. -/
theorem closed_package :
    Group.IsFinitelyPresented MFRadicalComputer.Carrier ∧
      ∀ T : ProofSystem, T.Sound →
        ∃ c : Code,
          codeWord c ≠ 1 ∧
            NormMFInvisible (codeWord c) ∧
            ¬ T.Proves c := by
  refine ⟨MFRadicalComputer.carrier_isFinitelyPresented, fun T hsound => ?_⟩
  obtain ⟨c, hne, hinvisible, _, hunproved⟩ :=
    exists_true_unprovable_radical_word T hsound
  exact ⟨c, hne, hinvisible, hunproved⟩

end

end MFRadicalGodel
end GroupApproximation
