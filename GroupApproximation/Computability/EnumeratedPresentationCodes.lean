import GroupApproximation.Higman.RelatorRE

/-!
# Standard codes for recursively enumerated group presentations

A code is an ordinary partial-recursive program.  An address is decoded as an
input/stage pair and the bounded evaluator is run at that pair.  A successful
output is decoded as a raw word; every failure contributes the empty word.
Thus every code determines a total enumeration of relators on the standard
countable alphabet, and every partial-recursive enumeration is represented up
to repetitions of the identity relator.

The word-problem checker below is primitive recursive uniformly in the
presentation code.  Its correctness is proved from the explicit raw
normal-closure certificate, rather than assumed as an interface.
-/

namespace GroupApproximation
namespace EnumeratedPresentationCodes

open Nat.Partrec
open Higman

noncomputable section

/-- The standard syntax of recursively enumerated countable presentations. -/
abbrev PresentationCode := Code

/-- Decode a natural number as a raw word, defaulting to the empty word. -/
def decodeRawWord (n : ℕ) : RawWord :=
  (Encodable.decode (α := RawWord) n).getD []

theorem primrec_decodeRawWord : Primrec decodeRawWord :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

/-- The relator at an address.  The address is `(input, stage)`. -/
def rawRelator (c : PresentationCode) (address : ℕ) : RawWord :=
  let p := Nat.unpair address
  (Code.evaln p.2 c p.1).map decodeRawWord |>.getD []

/-- Relator decoding is primitive recursive uniformly in the program code. -/
theorem primrec_rawRelator : Primrec₂ rawRelator := by
  have hp : Primrec fun z : PresentationCode × ℕ => Nat.unpair z.2 :=
    Primrec.unpair.comp Primrec.snd
  have heval : Primrec fun z : PresentationCode × ℕ =>
      Code.evaln (Nat.unpair z.2).2 z.1 (Nat.unpair z.2).1 :=
    Code.primrec_evaln.comp
      (Primrec.pair
        (Primrec.pair (Primrec.snd.comp hp) Primrec.fst)
        (Primrec.fst.comp hp))
  exact (Primrec.option_getD.comp
    (Primrec.option_map heval
      (primrec_decodeRawWord.comp Primrec.snd).to₂)
    (Primrec.const [])).to₂

/-- The relator set enumerated by a standard presentation code. -/
def relatorSet (c : PresentationCode) : Set (FreeGroup ℕ) :=
  Set.range fun address => freeEval (rawRelator c address)

/-- The group denoted by a standard recursively enumerated presentation. -/
abbrev Carrier (c : PresentationCode) : Type := PresentedGroup (relatorSet c)

/-- Total decoding of a free-reduction certificate. -/
def decodeSteps (n : ℕ) : List ℕ :=
  (Encodable.decode (α := List ℕ) n).getD []

theorem primrec_decodeSteps : Primrec decodeSteps :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

/-- A certificate that a raw word represents an enumerated relator or its
inverse.  The witness is `(address, (sign, reduction-steps-code))`. -/
def relatorCheck (c : PresentationCode) (v : RawWord) (witness : ℕ) : Bool :=
  let outer := Nat.unpair witness
  let inner := Nat.unpair outer.2
  let target := if inner.1 = 0 then rawRelator c outer.1
    else invRaw (rawRelator c outer.1)
  decide (Computability.applySteps (v ++ invRaw target)
    (decodeSteps inner.2) = some [])

/-- The symmetric-relator checker is primitive recursive uniformly in the
presentation code. -/
theorem primrec_relatorCheck :
    Primrec fun z : (PresentationCode × RawWord) × ℕ =>
      relatorCheck z.1.1 z.1.2 z.2 := by
  have hc : Primrec fun z : (PresentationCode × RawWord) × ℕ => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hv : Primrec fun z : (PresentationCode × RawWord) × ℕ => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have ho : Primrec fun z : (PresentationCode × RawWord) × ℕ => Nat.unpair z.2 :=
    Primrec.unpair.comp Primrec.snd
  have hi : Primrec fun z : (PresentationCode × RawWord) × ℕ =>
      Nat.unpair (Nat.unpair z.2).2 :=
    Primrec.unpair.comp (Primrec.snd.comp ho)
  have haddress : Primrec fun z : (PresentationCode × RawWord) × ℕ =>
      (Nat.unpair z.2).1 := Primrec.fst.comp ho
  have hsign : Primrec fun z : (PresentationCode × RawWord) × ℕ =>
      (Nat.unpair (Nat.unpair z.2).2).1 := Primrec.fst.comp hi
  have hsteps : Primrec fun z : (PresentationCode × RawWord) × ℕ =>
      decodeSteps (Nat.unpair (Nat.unpair z.2).2).2 :=
    primrec_decodeSteps.comp (Primrec.snd.comp hi)
  have hrel : Primrec fun z : (PresentationCode × RawWord) × ℕ =>
      rawRelator z.1.1 (Nat.unpair z.2).1 :=
    primrec_rawRelator.comp hc haddress
  have htarget : Primrec fun z : (PresentationCode × RawWord) × ℕ =>
      if (Nat.unpair (Nat.unpair z.2).2).1 = 0 then
        rawRelator z.1.1 (Nat.unpair z.2).1
      else invRaw (rawRelator z.1.1 (Nat.unpair z.2).1) :=
    Primrec.ite (Primrec.eq.comp hsign (Primrec.const 0)) hrel
      (primrec_invRaw.comp hrel)
  have hword : Primrec fun z : (PresentationCode × RawWord) × ℕ =>
      z.1.2 ++ invRaw
        (if (Nat.unpair (Nat.unpair z.2).2).1 = 0 then
          rawRelator z.1.1 (Nat.unpair z.2).1
        else invRaw (rawRelator z.1.1 (Nat.unpair z.2).1)) :=
    Primrec.list_append.comp hv (primrec_invRaw.comp htarget)
  exact (Primrec.eq.comp
    (Computability.primrec_applySteps.comp hword hsteps)
    (Primrec.const (some []))).decide.of_eq fun _ => by
      simp only [relatorCheck]

/-- Exact certificate semantics for membership in the symmetrized relator
set. -/
theorem freeEval_mem_symmetrize_iff (c : PresentationCode) (v : RawWord) :
    freeEval v ∈ symmetrize (relatorSet c) ↔
      ∃ witness, relatorCheck c v witness = true := by
  constructor
  · rintro (hv | ⟨r, hr, hrv⟩)
    · obtain ⟨address, haddress⟩ := hv
      obtain ⟨steps, hsteps⟩ := (freeEval_eq_one_iff
        (v ++ invRaw (rawRelator c address))).1 (by
          change evalRaw FreeGroup.of (rawRelator c address) =
            evalRaw FreeGroup.of v at haddress
          change evalRaw FreeGroup.of (v ++ invRaw (rawRelator c address)) = 1
          rw [evalRaw_append, evalRaw_invRaw, ← haddress, mul_inv_cancel])
      refine ⟨Nat.pair address (Nat.pair 0 (Encodable.encode steps)), ?_⟩
      simp [relatorCheck, decodeSteps, hsteps]
    · obtain ⟨address, rfl⟩ := hr
      obtain ⟨steps, hsteps⟩ := (freeEval_eq_one_iff
        (v ++ invRaw (invRaw (rawRelator c address)))).1 (by
          change (evalRaw FreeGroup.of (rawRelator c address))⁻¹ =
            evalRaw FreeGroup.of v at hrv
          change evalRaw FreeGroup.of
            (v ++ invRaw (invRaw (rawRelator c address))) = 1
          rw [evalRaw_append, evalRaw_invRaw, evalRaw_invRaw]
          rw [← hrv]
          simp)
      refine ⟨Nat.pair address (Nat.pair 1 (Encodable.encode steps)), ?_⟩
      simp [relatorCheck, decodeSteps, hsteps]
  · rintro ⟨witness, hw⟩
    simp only [relatorCheck, decide_eq_true_eq] at hw
    let outer := Nat.unpair witness
    let inner := Nat.unpair outer.2
    let target := if inner.1 = 0 then rawRelator c outer.1
      else invRaw (rawRelator c outer.1)
    have hone : freeEval (v ++ invRaw target) = 1 :=
      (freeEval_eq_one_iff _).2 ⟨decodeSteps inner.2, hw⟩
    have heq : freeEval v = freeEval target := by
      change evalRaw FreeGroup.of v = evalRaw FreeGroup.of target
      apply mul_inv_eq_one.mp
      change evalRaw FreeGroup.of (v ++ invRaw target) = 1 at hone
      simpa only [evalRaw_append, evalRaw_invRaw] using hone
    by_cases hsign : inner.1 = 0
    · exact Or.inl ⟨outer.1, by simpa [target, hsign] using heq.symm⟩
    · apply Or.inr
      refine ⟨freeEval (rawRelator c outer.1), ⟨outer.1, rfl⟩, ?_⟩
      calc
        (freeEval (rawRelator c outer.1))⁻¹ =
            freeEval (invRaw (rawRelator c outer.1)) := by
              exact (evalRaw_invRaw FreeGroup.of _).symm
        _ = freeEval v := by simpa [target, hsign] using heq.symm

/-- A numerical word-problem certificate for an enumerated presentation. -/
abbrev WordCertificate := RelCert

/-- The uniform word-problem checker. -/
def wordCheck (x : PresentationCode × RawWord) (cert : WordCertificate) : Bool :=
  relCert (relatorCheck x.1) x.2 cert

/-- The uniform word-problem checker is primitive recursive. -/
theorem primrec_wordCheck : Primrec₂ wordCheck := by
  have hmatch : PrimrecRel fun (q : (RawWord × RawWord) × ℕ)
      (y : (RawWord × RawWord) ×
        ((PresentationCode × RawWord) × WordCertificate)) =>
        q.1 = y.1 ∧ relatorCheck y.2.1.1 q.1.2 q.2 = true := by
    refine PrimrecPred.and ?_ ?_
    · exact Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)
    · refine Primrec.eq.comp ?_ (Primrec.const true)
      exact primrec_relatorCheck.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst))
  have hex : PrimrecRel fun (L : List ((RawWord × RawWord) × ℕ))
      (y : (RawWord × RawWord) ×
        ((PresentationCode × RawWord) × WordCertificate)) =>
        ∃ q ∈ L, q.1 = y.1 ∧ relatorCheck y.2.1.1 q.1.2 q.2 = true :=
    PrimrecRel.exists_mem_list hmatch
  have hitem : PrimrecRel fun (p : RawWord × RawWord)
      (x : (PresentationCode × RawWord) × WordCertificate) =>
        ∃ q ∈ x.2.2.1, q.1 = p ∧ relatorCheck x.1.1 q.1.2 q.2 = true :=
    PrimrecRel.comp hex
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.pair Primrec.fst Primrec.snd)
  have hall : PrimrecRel fun (L : List (RawWord × RawWord))
      (x : (PresentationCode × RawWord) × WordCertificate) =>
        ∀ p ∈ L,
          ∃ q ∈ x.2.2.1, q.1 = p ∧ relatorCheck x.1.1 q.1.2 q.2 = true :=
    PrimrecRel.forall_mem_list hitem
  have hlook : PrimrecPred fun x :
      (PresentationCode × RawWord) × WordCertificate =>
      ∀ p ∈ x.2.1,
        ∃ q ∈ x.2.2.1, q.1 = p ∧ relatorCheck x.1.1 q.1.2 q.2 = true :=
    PrimrecRel.comp hall (Primrec.fst.comp Primrec.snd) Primrec.id
  have hsteps : PrimrecPred fun x :
      (PresentationCode × RawWord) × WordCertificate =>
      Computability.applySteps (conjWord₂ x.2.1 ++ invRaw x.1.2) x.2.2.2
        = some [] := by
    refine Primrec.eq.comp ?_ (Primrec.const (some []))
    refine Computability.primrec_applySteps.comp ?_
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact Primrec.list_append.comp
      (primrec_conjWord₂.comp (Primrec.fst.comp Primrec.snd))
      (primrec_invRaw.comp (Primrec.snd.comp Primrec.fst))
  haveI : DecidablePred fun x :
      (PresentationCode × RawWord) × WordCertificate =>
      RelSolves (relatorCheck x.1.1) x.1.2 x.2 :=
    fun x => relSolves_decidable (relatorCheck x.1.1) x.1.2 x.2
  exact (PrimrecPred.and hlook hsteps).decide.of_eq fun _ => by
    unfold wordCheck relCert
    exact decide_eq_decide.mpr Iff.rfl

/-- The uniform checker recognizes exactly the word problem of the denoted
group. -/
theorem wordCheck_complete (c : PresentationCode) (w : RawWord) :
    evalRaw (fun k => (PresentedGroup.of k : Carrier c)) w = 1 ↔
      ∃ cert : WordCertificate, wordCheck (c, w) cert = true :=
  evalRaw_eq_one_iff_relCert (relatorCheck c)
    (fun k => (PresentedGroup.of k : Carrier c)) (relatorSet c)
    (evalRaw_presentedGroup_eq_one_iff (relatorSet c))
    (freeEval_mem_symmetrize_iff c) w

/-- Every standard presentation code denotes a recursively presented group. -/
def recursivePresentation (c : PresentationCode) :
    RecursivePresentation (Carrier c) :=
  recursivePresentationPresentedGroup (relCheck := relatorCheck c) (relatorSet c)
    (by
      exact (primrec_relatorCheck.comp
        (Primrec.pair
          (Primrec.pair (Primrec.const c) Primrec.fst)
          Primrec.snd)).to₂)
    (freeEval_mem_symmetrize_iff c)

end

end EnumeratedPresentationCodes
end GroupApproximation
