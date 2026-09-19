import GroupApproximation.GGT.HullSCRelatorSeparation2Span
import GroupApproximation.GGT.HullSCRelatorSeparation2MirrorBall
import GroupApproximation.GGT.HullSCRelatorSeparation2MixedCase

/-!
# The four per-case extractions

`GGT.OsinComponents.exists_two_block_conj_of_rot` concludes with two gaps in
`D.relBall lam (C · 4)` and a relation between the two components' SPANS.  Each
case of Olshanskii's step (c) turns that conclusion into its closer's input, and
this module is the four conversions.  They take the packaged theorem's
CONCLUSION, not its hypotheses: what it asks of a configuration is the caller's
to supply and is still being fixed, but what it delivers is settled, and these
are written against that.

The conversion itself is one step, `GGT/HullSCRelatorSeparation2Span.lean`: over
the alternating relator a component of the run spans a single letter, so the
span is the power the letter carries, and the relation between spans is the
relation between powers the rigidity reads.  The radius is the packaged
theorem's: a caller runs the design at `eps = C * 4`, which is what puts its
gaps in the ball the design's clauses quantify over.

* `conj_of_span_rot` -- both members rotations of the relator.
* `conj_of_span_inv` -- both rotations of the formal inverse.
* `false_of_span_mixed` -- one of each; two matched pairs, and the gap bound.
  The other mixed order is this one with the two members exchanged, the identity
  it rests on being symmetric in them.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Extract

variable {G : Type u} [Group G]

/-- **Both members rotations of the relator.** -/
theorem conj_of_span_rot {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps : ℕ}
    {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i j : ℕ}
    (hi : i < (relatorWord₂ p (a false) (a true) ms).length)
    (hj : j < (relatorWord₂ p (a false) (a true) ms).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' y : G}
    (hx : x ∈ D.relBall b eps) (hx' : x' ∈ D.relBall b eps)
    (hx'1 : x' = 1)
    (hlet : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)))
    (hlet' : ((relatorWord₂ p (a false) (a true) ms).rotate c')[j]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ f)))
    (hspan : x * ((GGT.OsinComponents.vertex (1 : G)
            ((relatorWord₂ p (a false) (a true) ms).rotate c) i)⁻¹ *
          GGT.OsinComponents.vertex (1 : G)
            ((relatorWord₂ p (a false) (a true) ms).rotate c) (i + 1)) * x'
      = (GGT.OsinComponents.vertex (1 : G)
            ((relatorWord₂ p (a false) (a true) ms).rotate c') j)⁻¹ *
          GGT.OsinComponents.vertex (1 : G)
            ((relatorWord₂ p (a false) (a true) ms).rotate c') (j + 1))
    (hy : y * GGT.OsinComponents.vertex (1 : G)
          ((relatorWord₂ p (a false) (a true) ms).rotate c) i * x'
      = GGT.OsinComponents.vertex (1 : G)
          ((relatorWord₂ p (a false) (a true) ms).rotate c') j) :
    GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c')
      = y * GGT.RelLetter.listVal
          ((relatorWord₂ p (a false) (a true) ms).rotate c) * y⁻¹ := by
  rw [span_eq_pow_of_block hlet, span_eq_pow_of_block hlet'] at hspan
  exact listVal_conj_of_alignedMatch_ball hnodup hinj hsep hi hj he hf
    hx hx' hspan hx'1 hlet hlet' hy

/-- **Both members rotations of the formal inverse.** -/
theorem conj_of_span_inv {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps : ℕ}
    {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i j : ℕ}
    (hi : i < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    (hj : j < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' y : G}
    (hx : x ∈ D.relBall b eps) (hx' : x' ∈ D.relBall b eps)
    (hx1 : x = 1)
    (hlet : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[i]?
      = some (GGT.RelLetter.comp b (((if b then a true else a false) ^ e)⁻¹)))
    (hlet' : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j]?
      = some (GGT.RelLetter.comp b (((if b then a true else a false) ^ f)⁻¹)))
    (hspan : x * ((GGT.OsinComponents.vertex (1 : G)
            ((RelWord.revInv
              (relatorWord₂ p (a false) (a true) ms)).rotate c) i)⁻¹ *
          GGT.OsinComponents.vertex (1 : G)
            ((RelWord.revInv
              (relatorWord₂ p (a false) (a true) ms)).rotate c) (i + 1)) * x'
      = (GGT.OsinComponents.vertex (1 : G)
            ((RelWord.revInv
              (relatorWord₂ p (a false) (a true) ms)).rotate c') j)⁻¹ *
          GGT.OsinComponents.vertex (1 : G)
            ((RelWord.revInv
              (relatorWord₂ p (a false) (a true) ms)).rotate c') (j + 1))
    (hy : y * GGT.OsinComponents.vertex (1 : G)
          ((RelWord.revInv
            (relatorWord₂ p (a false) (a true) ms)).rotate c) i * x'
      = GGT.OsinComponents.vertex (1 : G)
          ((RelWord.revInv
            (relatorWord₂ p (a false) (a true) ms)).rotate c') j) :
    GGT.RelLetter.listVal
        ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')
      = y * GGT.RelLetter.listVal
          ((RelWord.revInv
            (relatorWord₂ p (a false) (a true) ms)).rotate c) * y⁻¹ := by
  rw [span_eq_pow_inv_of_block hlet, span_eq_pow_inv_of_block hlet'] at hspan
  exact listVal_conj_of_mirroredAlignedMatch_ball hnodup hinj hsymm hsep
    hi hj he hf hx hx' hspan hx1 hlet hlet' hy

/-- **One member a rotation of the relator, the other of its formal inverse.**

Two matched pairs, converted by the same span step: each gives
`x · a^e · x' = (a^f)⁻¹`, which is the mirrored half of the separation clause,
so the exponents agree at both, and the gap identity closes the case. -/
theorem false_of_span_mixed {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps : ℕ}
    {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i₁ i₂ j₁ j₂ gapSlack : ℕ}
    (hi₂ : i₂ < (relatorWord₂ p (a false) (a true) ms).length)
    (hj₂ : j₂ < (relatorWord₂ p (a false) (a true) ms).length)
    (hii : i₁ < i₂) (hjj : j₁ < j₂)
    {b₁ b₂ : Bool} {e₁ f₁ e₂ f₂ : ℕ}
    (he₁ : e₁ ∈ ms) (hf₁ : f₁ ∈ ms) (he₂ : e₂ ∈ ms) (hf₂ : f₂ ∈ ms)
    {x₁ x₁' x₂ x₂' : G}
    (hx₁ : x₁ ∈ D.relBall b₁ eps) (hx₁' : x₁' ∈ D.relBall b₁ eps)
    (hx₂ : x₂ ∈ D.relBall b₂ eps) (hx₂' : x₂' ∈ D.relBall b₂ eps)
    (hl₁ : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i₁]?
      = some (GGT.RelLetter.comp b₁ ((if b₁ then a true else a false) ^ e₁)))
    (hm₁ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j₁]?
      = some (GGT.RelLetter.comp b₁ (((if b₁ then a true else a false) ^ f₁)⁻¹)))
    (hl₂ : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i₂]?
      = some (GGT.RelLetter.comp b₂ ((if b₂ then a true else a false) ^ e₂)))
    (hm₂ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j₂]?
      = some (GGT.RelLetter.comp b₂ (((if b₂ then a true else a false) ^ f₂)⁻¹)))
    (hconn₁ : x₁ * a b₁ ^ e₁ * x₁' = (a b₁ ^ f₁)⁻¹)
    (hconn₂ : x₂ * a b₂ ^ e₂ * x₂' = (a b₂ ^ f₂)⁻¹)
    (hclose : j₂ - j₁ ≤ i₂ - i₁ + gapSlack)
    (hsmall : 2 * (i₂ - i₁) + gapSlack
      < (relatorWord₂ p (a false) (a true) ms).length) : False := by
  have hef₁ : e₁ = f₁ :=
    exponent_eq_of_mirroredBlockMatch_ball hsep he₁ hf₁ hx₁ hx₁' hconn₁
  have hef₂ : e₂ = f₂ :=
    exponent_eq_of_mirroredBlockMatch_ball hsep he₂ hf₂ hx₂ hx₂' hconn₂
  have hinj' : ∀ t : Bool,
      Function.Injective (fun n : ℕ => (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  exact not_mirroredMatch_of_gap hinj' hnodup hi₂ hj₂ hii hjj hef₁ hef₂
    hl₁ hm₁ hl₂ hm₂ hclose hsmall

end Extract

end HullSC
end GroupApproximation
