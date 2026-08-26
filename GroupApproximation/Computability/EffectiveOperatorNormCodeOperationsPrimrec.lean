import GroupApproximation.Computability.EffectiveOperatorNormCodeCore

/-!
# Primitive-recursive operator-norm certificate operations

The executable power and Frobenius operations are audited here separately from
the analytic certificate semantics and the final predicates.
-/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec

open OperatorNormCertificate

/-! ## Primitive-recursive audit -/

theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primrec_ratOfNat : Primrec ratOfNat :=
  Primrec.pair (Primrec.pair Primrec.id (Primrec.const 0)) (Primrec.const 0)

theorem primrec_ratInvSucc : Primrec ratInvSucc :=
  Primrec.pair (Primrec.const (1, 0)) Primrec.id

theorem primrec_ratPow : Primrec₂ ratPow := by
  have hstep : Primrec₂ fun q (p : ℕ × RatCode) => ratMul p.2 q :=
    primrec_ratMul.comp₂ (Primrec.snd.comp₂ Primrec₂.right) Primrec₂.left
  refine (Primrec.nat_rec (Primrec.const ratOne) hstep).of_eq ?_
  intro q n
  induction n with
  | zero => rfl
  | succ n ih => simp only [ratPow, ih]

theorem primrec_matrixPow :
    Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      matrixPow z.1.1 z.1.2 z.2 := by
  have hbase : Primrec fun p : ℕ × MatrixCode => identity p.1 :=
    primrec_identity.comp Primrec.fst
  have hstep : Primrec₂ fun (p : ℕ × MatrixCode)
      (s : ℕ × MatrixCode) => matrixMul p.1 s.2 p.2 := by
    exact (primrec_matrixMul.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst))).to₂
  refine (Primrec.nat_rec hbase hstep).of_eq ?_
  intro p n
  induction n with
  | zero => rfl
  | succ n ih => simp only [matrixPow, ih]

theorem primrec_froRowSqCode :
    Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      froRowSqCode z.1.1 z.1.2 z.2 := by
  have hrange : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      List.range (dim z.1.1) :=
    Primrec.list_range.comp
      (primrec_dim.comp (Primrec.fst.comp Primrec.fst))
  have hstep : Primrec₂ fun (z : (ℕ × MatrixCode) × ℕ)
      (p : RatCode × ℕ) =>
      ratAdd p.1 (complexNormSq (entry z.1.1 z.1.2 z.2 p.2)) := by
    have hentry : Primrec fun q : ((ℕ × MatrixCode) × ℕ) ×
        (RatCode × ℕ) => entry q.1.1.1 q.1.1.2 q.1.2 q.2.2 :=
      primrec_entry.comp (Primrec.pair
        (Primrec.pair
          (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
    exact (primrec_ratAdd.comp (Primrec.fst.comp Primrec.snd)
      (primrec_complexNormSq.comp hentry)).to₂
  exact Primrec.list_foldl hrange (Primrec.const ratZero) hstep

theorem primrec_froSqCode :
    Primrec fun z : ℕ × MatrixCode => froSqCode z.1 z.2 := by
  have hrange : Primrec fun z : ℕ × MatrixCode => List.range (dim z.1) :=
    Primrec.list_range.comp (primrec_dim.comp Primrec.fst)
  have hstep : Primrec₂ fun (z : ℕ × MatrixCode) (p : RatCode × ℕ) =>
      ratAdd p.1 (froRowSqCode z.1 z.2 p.2) := by
    have hrow : Primrec fun q : (ℕ × MatrixCode) × (RatCode × ℕ) =>
        froRowSqCode q.1.1 q.1.2 q.2.2 :=
      primrec_froRowSqCode.comp
        (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
    exact (primrec_ratAdd.comp (Primrec.fst.comp Primrec.snd) hrow).to₂
  exact Primrec.list_foldl hrange (Primrec.const ratZero) hstep

theorem primrec_gramPowCode :
    Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      gramPowCode z.1.1 z.1.2 z.2 := by
  have hd : Primrec fun z : (ℕ × MatrixCode) × ℕ => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hA : Primrec fun z : (ℕ × MatrixCode) × ℕ => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hstar : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      conjTranspose z.1.1 z.1.2 :=
    primrec_conjTranspose.comp (Primrec.pair hd hA)
  have hgram : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      matrixMul z.1.1 (conjTranspose z.1.1 z.1.2) z.1.2 :=
    primrec_matrixMul.comp (Primrec.pair (Primrec.pair hd hstar) hA)
  have hexp : Primrec fun z : (ℕ × MatrixCode) × ℕ => 2 ^ z.2 :=
    primrec_natPow.comp (Primrec.const 2) Primrec.snd
  exact primrec_matrixPow.comp
    (Primrec.pair (Primrec.pair hd hgram) hexp)

end EffectiveOperatorNormCode
end GroupApproximation
