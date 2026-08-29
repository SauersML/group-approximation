import GroupApproximation.GGT.HullSCRelatorSeparation2AlignedClose

/-!
# The fourth case: both members rotations of the formal inverse

`GGT/HullSCRelatorSeparation2AlignedClose.lean` closes the case where both
members of the symmetrized closure are rotations of the relator.  Here both are
rotations of its formal inverse, and the argument is the same one read through
an inversion.

The letters of `RelWord.revInv` carry the inverses of the powers the relator's
letters carry, so `exists_block_span_conj`'s relation `x · v_q · x' = v_s`
arrives as `x · (a^e)⁻¹ · x' = (a^f)⁻¹`.  Inverting it gives
`x'⁻¹ · a^e · x⁻¹ = a^f`, which is the direct shape with the two gaps swapped
and inverted -- and the base being symmetric, inversion does not change a word
norm, so the two gaps are still short.  From there the rigidity, the diagonal
clause and the join apply verbatim, through
`HullSC.position_eq_of_alignedMatch_revInv` in place of its direct twin.

That the swap is harmless is worth one remark: the rigidity is symmetric in its
two gaps in the sense that both are merely required to be short, so nothing
distinguishes them, and `HullSC.trivial_connector_of_alignedMatch` returns the
triviality of each.  Reading them back through the inversion returns the
triviality of the original two.

With this the four cases of Olshanskii's step (c) are closed from the
quadrilateral's own output.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section MirrorClose

variable {G : Type u} [Group G]

/-- **At a matched block of the mirrored aligned case the connectors are
trivial.**  The inverted relation is the direct one with the gaps swapped. -/
theorem trivial_connector_of_mirroredAlignedMatch {D : GGT.RelGenSet G Bool}
    (hbase : IsSymmetricGeneratingSet D.base) {a : Bool → G} {eps rho : ℕ}
    {ms : List ℕ} {s : Bool}
    (hgeo : ∀ (i j : ℕ) (x x' : G), wordNorm D.base x ≤ eps →
      wordNorm D.base x' ≤ eps → a s ^ i ∉ D.relBall s rho →
        a s ^ j ∉ D.relBall s rho → x * a s ^ i * x' = a s ^ j →
          x ∈ D.fam s ∧ x' ∈ D.fam s)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdiag : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * a t ^ i * x' ≠ a t ^ i)
    {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' : G}
    (hx : wordNorm D.base x ≤ eps) (hx' : wordNorm D.base x' ≤ eps)
    (hconn : x * (a s ^ e)⁻¹ * x' = (a s ^ f)⁻¹) : e = f ∧ x = 1 ∧ x' = 1 := by
  have hinv : x'⁻¹ * a s ^ e * x⁻¹ = a s ^ f := by
    have h := congrArg (fun g : G => g⁻¹) hconn
    simpa [mul_inv_rev, mul_assoc] using h
  have hnx'inv : wordNorm D.base x'⁻¹ ≤ eps := by
    rw [wordNorm_inv hbase]
    exact hx'
  have hnxinv : wordNorm D.base x⁻¹ ≤ eps := by
    rw [wordNorm_inv hbase]
    exact hx
  obtain ⟨hef, hx'1, hx1⟩ :=
    trivial_connector_of_alignedMatch hbase hgeo hdeep hsep hdiag he hf
      hnx'inv hnxinv hinv
  exact ⟨hef, inv_eq_one.mp hx1, inv_eq_one.mp hx'1⟩

/-- **The mirrored aligned case, closed from the polygon's output.** -/
theorem listVal_conj_of_mirroredAlignedMatch {D : GGT.RelGenSet G Bool}
    (hbase : IsSymmetricGeneratingSet D.base) {a : Bool → G} {eps rho : ℕ}
    {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hgeo : ∀ (s : Bool) (i j : ℕ) (x x' : G), wordNorm D.base x ≤ eps →
      wordNorm D.base x' ≤ eps → a s ^ i ∉ D.relBall s rho →
        a s ^ j ∉ D.relBall s rho → x * a s ^ i * x' = a s ^ j →
          x ∈ D.fam s ∧ x' ∈ D.fam s)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdiag : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * a t ^ i * x' ≠ a t ^ i)
    {p : List G} {c c' i j : ℕ}
    (hi : i < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    (hj : j < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' y : G}
    (hnx : wordNorm D.base x ≤ eps) (hnx' : wordNorm D.base x' ≤ eps)
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
    trivial_connector_of_mirroredAlignedMatch hbase (hgeo b) hdeep hsep hdiag
      he hf hnx hnx' hconn
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

end MirrorClose

end HullSC
end GroupApproximation
