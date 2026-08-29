import GroupApproximation.GGT.HullSCRelatorSeparation2Ball
import GroupApproximation.GGT.HullSCRelatorSeparation2MirrorClose

/-!
# The mirrored aligned case in ball currency

`GGT/HullSCRelatorSeparation2Ball.lean` puts the aligned case in the currency
`GGT.OsinComponents.exists_two_block_conj_of_innermost` pays in.  This module
does the same for the case where both members are rotations of the formal
inverse, and one thing changes that is not bookkeeping.

The letters of `RelWord.revInv` carry inverses, so the packaged theorem's
relation arrives with an inverse on BOTH sides: `x · (a^e)⁻¹ · x' = (a^f)⁻¹`.
Neither existing clause of the design is in that shape — the mirrored half of
the separation clause is `x · a^i · x' ≠ (a^j)⁻¹`, with a direct power on the
left — so this case needs the two inverted clauses `hsepInv` and `hdiagInv`,
carried here as hypotheses.  They are genuine new obligations on the design, not
restatements of old ones, and I would rather name them than quietly invert
something.

The word-norm route did not need them because a word norm is inversion
invariant, so `GGT/HullSCRelatorSeparation2MirrorClose.lean` could invert the
relation and use the direct clauses.  In ball currency that step needs the
relative ball to be closed under inverses, which is TRUE but is a small theorem
rather than a rewrite: for `x ∈ H_λ`, the word `revInv w` spells `x⁻¹`, is
admissible when the base is symmetric, and still avoids `Γ_{H λ}` because its
vertices are the original ones right-translated by `x⁻¹ ∈ H_λ`, which does not
change whether a vertex lies in `H_λ`.  Either route closes the case; this file
takes the one that adds hypotheses rather than the one that adds a theorem, so
that whoever supplies the design decides which.

How it is produced, so that the obligation is not left vague: the inverted
diagonal for `(x, x')` at `i` is the direct diagonal for `(x'⁻¹, x⁻¹)` at `i`,
so the exponents it forbids are those of `HullSC.diagonalBad a (T ∪ T⁻¹)`, which
is finite by `HullSC.finite_diagonalBad` — the ball need not be closed under
inverses, since the union is finite either way — and the leaf that clause rests
on extends to inverses by `Commute.inv_left`, an element and its inverse
commuting with exactly the same things.  The greedy step then avoids it as it
avoids the direct one.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section MirrorBall

variable {G : Type u} [Group G]

/-- **At a matched block of the mirrored aligned case the connectors are
trivial**, from ball membership. -/
theorem trivial_connector_of_mirroredAlignedMatch_ball
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps : ℕ} {ms : List ℕ}
    {s : Bool}
    (hsepInv : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x * (a t ^ i)⁻¹ * x' ≠ (a t ^ j)⁻¹)
    (hdiagInv : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * (a t ^ i)⁻¹ * x' ≠ (a t ^ i)⁻¹)
    {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' : G}
    (hx : x ∈ D.relBall s eps) (hx' : x' ∈ D.relBall s eps)
    (hconn : x * (a s ^ e)⁻¹ * x' = (a s ^ f)⁻¹) : e = f ∧ x = 1 ∧ x' = 1 := by
  have hef : e = f := by
    by_contra hij
    exact hsepInv e he f hf hij s x hx x' hx' hconn
  subst hef
  have hx1 : x = 1 := by
    by_contra hne
    exact hdiagInv e he s x hx x' hx' hne hconn
  refine ⟨rfl, hx1, ?_⟩
  rw [hx1, one_mul] at hconn
  exact mul_eq_left.mp hconn

/-- **The mirrored aligned case, closed from the packaged theorem's output.** -/
theorem listVal_conj_of_mirroredAlignedMatch_ball {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsepInv : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x * (a t ^ i)⁻¹ * x' ≠ (a t ^ j)⁻¹)
    (hdiagInv : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * (a t ^ i)⁻¹ * x' ≠ (a t ^ i)⁻¹)
    {p : List G} {c c' i j : ℕ}
    (hi : i < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    (hj : j < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' y : G}
    (hx : x ∈ D.relBall b eps) (hx' : x' ∈ D.relBall b eps)
    (hconn : x * (a b ^ e)⁻¹ * x' = (a b ^ f)⁻¹)
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
    trivial_connector_of_mirroredAlignedMatch_ball hsepInv hdiagInv he hf hx hx' hconn
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
