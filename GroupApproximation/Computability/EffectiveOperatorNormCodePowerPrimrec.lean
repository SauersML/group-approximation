import GroupApproximation.Computability.EffectiveOperatorNormCodeCore

/-! Primitive-recursive rational and coded-matrix powers for norm certificates. -/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec

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
  have hrec : Primrec₂ fun (p : ℕ × MatrixCode) (n : ℕ) =>
      matrixPow p.1 p.2 n := by
    refine (Primrec.nat_rec hbase hstep).of_eq ?_
    intro p n
    induction n with
    | zero => rfl
    | succ n ih => simp only [matrixPow, ih]
  exact hrec.comp Primrec.fst Primrec.snd

end EffectiveOperatorNormCode
end GroupApproximation
