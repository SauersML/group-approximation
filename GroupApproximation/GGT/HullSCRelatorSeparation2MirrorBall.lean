import GroupApproximation.GGT.HullSCRelatorSeparation2Ball
import GroupApproximation.GGT.HullSCRelatorSeparation2MirrorClose
import GroupApproximation.GGT.OsinTheorem54SepReversal

/-!
# The mirrored aligned case in ball currency

`GGT/HullSCRelatorSeparation2Ball.lean` puts the aligned case in the currency
`GGT.OsinComponents.exists_two_block_conj_of_rot` pays in.  This module
does the same for the case where both members are rotations of the formal
inverse, and one thing changes that is not bookkeeping.

The letters of `RelWord.revInv` carry inverses, so the packaged theorem's
relation arrives with an inverse on BOTH sides: `x · (a^e)⁻¹ · x' = (a^f)⁻¹`.
Neither clause of the design is in that shape -- the mirrored half of the
separation clause is `x · a^i · x' ≠ (a^j)⁻¹`, with a direct power on the left.

Rather than burden the design with two more clauses, the relation is inverted:
`x' ⁻¹ · a^e · x⁻¹ = a^f` is the direct shape, and the direct clauses apply to
it once the two gaps are known to be in the ball again.  That is
`inv_mem_relBall`, and it holds for the reason the relative metric is
left-invariant on `H_λ`: the reversed word spells the inverse, is admissible
when the base is symmetric, and avoids `Γ_{H λ}` from the far end exactly when
the original avoids it from the near end -- `avoidsFrom_revWord` -- after which
translating the basepoint back by `x⁻¹ ∈ H_λ` is `avoidsFrom_smul_left`.

So the design owes nothing new, and the mirrored case runs on the same clauses
as the direct one.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section MirrorBall

variable {G : Type u} [Group G]

/-- **The relative ball is closed under inverses.**

The reversed word spells the inverse and is admissible when the base is
symmetric; it avoids `Γ_{H λ}` from the far end exactly when the original avoids
it from the near end, and the far end is `x`, which lies in `H λ`, so
translating the basepoint back to `1` is left-invariance on `H λ`. -/
theorem inv_mem_relBall {Λ : Type*} {D : GGT.RelGenSet G Λ} {lam : Λ} {n : ℕ}
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base) {x : G} (hx : x ∈ D.relBall lam n) :
    x⁻¹ ∈ D.relBall lam n := by
  rw [GGT.RelGenSet.mem_relBall] at hx ⊢
  obtain ⟨hfam, w, hlet, hval, havoid, hlen⟩ := hx
  refine ⟨inv_mem hfam, GGT.OsinComponents.revWord w,
    GGT.OsinComponents.isLetter_of_mem_revWord D hsymm hlet, ?_, ?_, ?_⟩
  · rw [GGT.OsinComponents.listVal_revWord, hval]
  · have hrev : GGT.AvoidsFrom D.fam lam
        (GGT.OsinComponents.revWord w) x := by
      have h := (GGT.OsinComponents.avoidsFrom_revWord D lam w hlet 1).mpr havoid
      rwa [one_mul, hval] at h
    have hshift := GGT.OsinComponents.avoidsFrom_smul_left (H := D.fam)
      (lam := lam) (c := x⁻¹) (inv_mem hfam) (GGT.OsinComponents.revWord w) x
    rw [inv_mul_cancel] at hshift
    exact hshift.mpr hrev
  · rw [GGT.OsinComponents.length_revWord]
    exact hlen

/-- **At a matched block of the mirrored aligned case the connectors are
trivial**, from ball membership. -/
theorem trivial_connector_of_mirroredAlignedMatch_ball
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps : ℕ} {ms : List ℕ}
    {s : Bool}
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' : G}
    (hx : x ∈ D.relBall s eps) (hx' : x' ∈ D.relBall s eps)
    (hconn : x * (a s ^ e)⁻¹ * x' = (a s ^ f)⁻¹) (hx1 : x = 1) :
    e = f ∧ x = 1 ∧ x' = 1 := by
  have hinvrel : x'⁻¹ * a s ^ e * x⁻¹ = a s ^ f := by
    have h := congrArg (fun g : G => g⁻¹) hconn
    simpa [mul_inv_rev, mul_assoc] using h
  obtain ⟨hef, hAinv, hBinv⟩ :=
    trivial_connector_of_alignedMatch_ball hsep he hf
      (inv_mem_relBall hsymm hx') (inv_mem_relBall hsymm hx) hinvrel
      (inv_eq_one.mpr hx1)
  exact ⟨hef, inv_eq_one.mp hBinv, inv_eq_one.mp hAinv⟩

/-- **The mirrored aligned case, closed from the packaged theorem's output.** -/
theorem listVal_conj_of_mirroredAlignedMatch_ball {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
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
    (hconn : x * (a b ^ e)⁻¹ * x' = (a b ^ f)⁻¹) (hx1 : x = 1)
    (hlet : ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c)[i]?
      = some (GGT.RelLetter.comp b (((if b then a true else a false) ^ e)⁻¹)))
    (hlet' : ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')[j]?
      = some (GGT.RelLetter.comp b (((if b then a true else a false) ^ f)⁻¹)))
    (hy : y * GGT.OsinComponents.vertex (1 : G)
          ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c) i * x'
      = GGT.OsinComponents.vertex (1 : G)
          ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c') j) :
    GGT.RelLetter.listVal
        ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')
      = y * GGT.RelLetter.listVal
          ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c) * y⁻¹ := by
  obtain ⟨hef, -, hx'1⟩ :=
    trivial_connector_of_mirroredAlignedMatch_ball hsymm hsep he hf hx hx'
      hconn hx1
  rw [hx'1, mul_one] at hy
  have hinj' : ∀ t : Bool,
      Function.Injective (fun n : ℕ => (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  refine listVal_conj_of_rotate_eq_of_vertex_eq ?_ ?_
    (rotate_eq_of_position_eq (RelWord.revInv (relatorWord₂ p (a false) (a true) ms))
      (position_eq_of_alignedMatch_revInv hinj' hnodup hi hj hef hlet hlet')) hy
  · rw [List.length_rotate]
    omega
  · rw [List.length_rotate]
    omega

end MirrorBall

end HullSC
end GroupApproximation
