import GroupApproximation.Computability.TorsionFreeEnumeratedHardness
import GroupApproximation.Computability.PerfectEnumeratedPi02

/-!
# Torsion-freeness of an enumerated presentation is `Π⁰₂`-complete

A group is power-torsion-free iff no word has a trivial positive power
while being nontrivial itself.  Written with the power's triviality
*certified* rather than merely asserted, the challenge becomes a single
existential over a decidable checker: "either this certificate does not
show `w^(n+1) = 1`, or some certificate shows `w = 1`".  So torsion-freeness
is `Π⁰₂`, and with the switch lower bound of
`Computability.TorsionFreeEnumeratedHardness` it is `Π⁰₂`-complete.
Research node `torsion-freeness-recognition-is-pi2-complete`.
-/

namespace GroupApproximation
namespace TorsionFreeEnumeratedPi02

open ArithmeticalHierarchy EnumeratedPresentationCodes Higman
open PerfectEnumeratedPi02

/-- The `n`-fold concatenation of a raw word. -/
def powRaw (w : RawWord) : ℕ → RawWord
  | 0 => []
  | n + 1 => w ++ powRaw w n

theorem evalRaw_powRaw {A : Type} [Group A] (x : ℕ → A) (w : RawWord) :
    ∀ n, evalRaw x (powRaw w n) = evalRaw x w ^ n
  | 0 => by simp [powRaw]
  | n + 1 => by rw [powRaw, evalRaw_append, evalRaw_powRaw x w n, pow_succ']

theorem primrec_powRaw : Primrec₂ powRaw := by
  have hstep : Primrec₂ fun (w : RawWord) (p : ℕ × RawWord) => w ++ p.2 :=
    (Primrec.list_append.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂
  refine (Primrec.nat_rec (Primrec.const ([] : RawWord)) hstep).of_eq ?_
  intro w n
  induction n with
  | zero => rfl
  | succ k ih => simp [powRaw, ih]

/-- The torsion challenge, indexed by a raw word, an exponent and a
certificate for the power, as a single existential over a decidable
check: either the given certificate fails to show `w^(n+1) = 1`, or some
certificate shows `w = 1`. -/
def TorsionAnswer (z : PresentationCode × (RawWord × ℕ × WordCertificate)) : Prop :=
  ∃ cert : WordCertificate,
    (!wordCheck (z.1, powRaw z.2.1 (z.2.2.1 + 1)) z.2.2.2
      || wordCheck (z.1, z.2.1) cert) = true

theorem torsionAnswer_iff (c : PresentationCode) (w : RawWord) (n : ℕ)
    (cert : WordCertificate) :
    TorsionAnswer (c, (w, n, cert)) ↔
      (wordCheck (c, powRaw w (n + 1)) cert = true →
        evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) w = 1) := by
  constructor
  · rintro ⟨cert', h⟩ hpow
    rw [hpow] at h
    simp only [Bool.not_true, Bool.false_or] at h
    exact (wordCheck_complete c w).2 ⟨cert', h⟩
  · intro h
    by_cases hpow : wordCheck (c, powRaw w (n + 1)) cert = true
    · obtain ⟨cert', hcert'⟩ := (wordCheck_complete c w).1 (h hpow)
      exact ⟨cert', by simp [hpow, hcert']⟩
    · refine ⟨cert, ?_⟩
      simp only [Bool.not_eq_true] at hpow
      simp [hpow]

/-- Torsion-freeness as a universal challenge. -/
theorem isPowerTorsionFree_iff_forall (c : PresentationCode) :
    IsPowerTorsionFree (Carrier c) ↔
      ∀ x : RawWord × ℕ × WordCertificate, TorsionAnswer (c, x) := by
  constructor
  · rintro h ⟨w, n, cert⟩
    rw [torsionAnswer_iff]
    intro hpow
    have hp : evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) w ^ (n + 1) = 1 := by
      have := (wordCheck_complete c (powRaw w (n + 1))).2 ⟨cert, hpow⟩
      rwa [evalRaw_powRaw] at this
    exact h _ (n + 1) (Nat.succ_pos n) hp
  · intro h g n hn hg
    obtain ⟨w, hw⟩ := exists_evalRaw c g
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
    have hpow : evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c))
        (powRaw w (m + 1)) = 1 := by
      rw [evalRaw_powRaw, hw]; exact hg
    obtain ⟨cert, hcert⟩ := (wordCheck_complete c _).1 hpow
    have := (torsionAnswer_iff c w m cert).1 (h (w, m, cert)) hcert
    rw [hw] at this
    exact this

/-- The challenge is recursively enumerable. -/
theorem rePred_torsionAnswer : REPred TorsionAnswer := by
  have hprim : Primrec₂ fun (z : PresentationCode × (RawWord × ℕ × WordCertificate))
      (cert : WordCertificate) =>
      (!wordCheck (z.1, powRaw z.2.1 (z.2.2.1 + 1)) z.2.2.2
        || wordCheck (z.1, z.2.1) cert) := by
    have hpow : Primrec fun z : PresentationCode × (RawWord × ℕ × WordCertificate) =>
        wordCheck (z.1, powRaw z.2.1 (z.2.2.1 + 1)) z.2.2.2 :=
      primrec_wordCheck.comp
        (Primrec.pair Primrec.fst
          (primrec_powRaw.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hw : Primrec₂ fun (z : PresentationCode × (RawWord × ℕ × WordCertificate))
        (cert : WordCertificate) => wordCheck (z.1, z.2.1) cert :=
      primrec_wordCheck.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        Primrec.snd
    exact (Primrec.dom_bool₂ (fun a b => !a || b)).comp (hpow.comp Primrec.fst) hw
  exact (WordProblemRE.rePred_exists_eq_true hprim.to_comp).of_eq fun _ => Iff.rfl

/-- **Torsion-freeness of enumerated presentation codes is `Π⁰₂`.** -/
theorem pi02_isPowerTorsionFree :
    Pi02 (fun c : PresentationCode ↦ IsPowerTorsionFree (Carrier c)) := by
  refine ⟨fun z : PresentationCode × ℕ ↦
    TorsionAnswer (z.1, (Encodable.decode (α := RawWord × ℕ × WordCertificate) z.2).getD
      ([], 0, default)), ?_, ?_⟩
  · exact rePred_torsionAnswer.comp
      (Computable.pair Computable.fst
        ((Computable.option_getD (Computable.decode.comp Computable.snd)
          (Computable.const ([], 0, default)))))
  · intro c
    show IsPowerTorsionFree (Carrier c) ↔ _
    rw [isPowerTorsionFree_iff_forall c]
    constructor
    · intro h n
      exact h _
    · intro h x
      have hx := h (Encodable.encode x)
      simpa using hx

/-- **Torsion-freeness of enumerated presentation codes is `Π⁰₂`-complete.** -/
theorem torsionFree_enum_pi02Complete :
    Pi02Complete (fun c : PresentationCode ↦ IsPowerTorsionFree (Carrier c)) :=
  ⟨pi02_isPowerTorsionFree, TorsionFreeEnumeratedHardness.torsionFreeCode_pi02Hard⟩

end TorsionFreeEnumeratedPi02
end GroupApproximation
