import GroupApproximation.Computability.ElementaryEnumeratedHardness
import GroupApproximation.Computability.WordProblemRE

/-!
# Triviality of an enumerated presentation is `Π⁰₂`-complete

The presented group is trivial iff every generator is trivial, and "generator
`n` is trivial" is the r.e. word problem of the enumerated presentation; so
triviality is `Π⁰₂`, and with the switch lower bound of
`ElementaryEnumeratedHardness` it is `Π⁰₂`-complete (research node
`arithmetical-complexity-table-of-group-properties`, the folklore first row).
-/

namespace GroupApproximation
namespace TrivialEnumeratedPi02

open ArithmeticalHierarchy EnumeratedPresentationCodes Higman

/-- The generator-triviality challenge: generator `n` is trivial in the
presented group, expressed through the uniform word checker. -/
def GenTrivial (z : PresentationCode × ℕ) : Prop :=
  ∃ cert : WordCertificate, wordCheck (z.1, [(z.2, true)]) cert = true

theorem genTrivial_iff (c : PresentationCode) (n : ℕ) :
    GenTrivial (c, n) ↔ (PresentedGroup.of n : Carrier c) = 1 := by
  unfold GenTrivial
  rw [← wordCheck_complete]
  simp

/-- A presented group whose generators are all trivial is trivial. -/
theorem subsingleton_of_forall_of (c : PresentationCode)
    (h : ∀ n, (PresentedGroup.of n : Carrier c) = 1) : Subsingleton (Carrier c) := by
  refine ⟨fun a b ↦ ?_⟩
  have key : ∀ x : Carrier c, x = 1 := by
    intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective x
    rw [← hy]
    refine FreeGroup.induction_on
      (C := fun y : FreeGroup ℕ => ((QuotientGroup.mk y : Carrier c) = 1)) y ?_ ?_ ?_ ?_
    · simp
    · intro k
      exact h k
    · intro k ih
      rw [QuotientGroup.mk_inv, ih, inv_one]
    · intro u v ihu ihv
      rw [QuotientGroup.mk_mul, ihu, ihv, one_mul]
  rw [key a, key b]

theorem subsingleton_iff (c : PresentationCode) :
    Subsingleton (Carrier c) ↔ ∀ n, GenTrivial (c, n) := by
  constructor
  · intro h n
    rw [genTrivial_iff]
    exact Subsingleton.elim _ _
  · intro h
    exact subsingleton_of_forall_of c fun n ↦ (genTrivial_iff c n).1 (h n)

theorem rePred_genTrivial : REPred GenTrivial := by
  have hcheck : Computable₂ fun (z : PresentationCode × ℕ) (cert : WordCertificate) =>
      wordCheck (z.1, [(z.2, true)]) cert := by
    have : Primrec₂ fun (z : PresentationCode × ℕ) (cert : WordCertificate) =>
        wordCheck (z.1, [(z.2, true)]) cert :=
      primrec_wordCheck.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.list_cons.comp
            (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.const true))
            (Primrec.const [])))
        Primrec.snd
    exact this.to_comp
  exact (WordProblemRE.rePred_exists_eq_true hcheck).of_eq fun _ => Iff.rfl

/-- **Triviality of enumerated presentation codes is `Π⁰₂`.** -/
theorem pi02_subsingleton :
    Pi02 (fun c : PresentationCode ↦ Subsingleton (Carrier c)) :=
  ⟨GenTrivial, rePred_genTrivial, fun c ↦ subsingleton_iff c⟩

/-- **Triviality of enumerated presentation codes is `Π⁰₂`-complete.** -/
theorem trivial_enum_pi02Complete :
    Pi02Complete (fun c : PresentationCode ↦ Subsingleton (Carrier c)) :=
  ⟨pi02_subsingleton, ElementaryEnumeratedHardness.trivialCode_pi02Hard⟩

end TrivialEnumeratedPi02
end GroupApproximation
