import GroupApproximation.GGT.HullSCRelatorSeparation2Join
import GroupApproximation.GGT.HullSCRelatorSeparation2MixedCase
import GroupApproximation.GGT.HullSCRelatorSeparation2Diagonal

/-!
# The aligned case, closed from the polygon's own output

`GGT/HullSCRelatorSeparation2Join.lean` closes the aligned case from a matched
block with **trivial** connectors.  The polygon delivers short ones, not trivial
ones, so one step is missing, and it is the diagonal clause of the design.

At a matched block in the aligned case the two letters carry powers of one and
the same element, and the rigidity makes the exponents agree, so the connector
relation `x · a^e · x' = a^f` collapses to the diagonal `x · a^e · x' = a^e`.
That is exactly what `GGT/HullSCRelatorSeparation2Diagonal.lean` forbids for
`x ≠ 1`: the connectors are trivial, and then the join applies.

So the chain for the aligned case is: matched block, rigidity, diagonal clause,
trivial connectors, Meet's vertex form, and the conjugation identity that
`RelWord.IsPiece` excludes -- with `y` the four-gon's own first side throughout.
No aperiodicity and no constraint on the offsets enter at any point.

`trivial_connector_of_alignedMatch` is the new step; `listVal_conj_of_alignedMatch`
is the composition.  The case where both members are rotations of the formal
inverse is the same argument through
`HullSC.position_eq_of_alignedMatch_revInv`, the connector relation being the
inverse of one of this shape.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Close

variable {G : Type u} [Group G]

/-- **At a matched block of the aligned case the connectors are trivial.**

The exponents agree by rigidity, so the relation is the diagonal.  The RIGHT
connector is trivial by (W4) --- `HullSC.secondGap_eq_one_of_next`, from the
match at the next component --- and the left one follows by cancellation.  The
direction used to run the other way, with a design clause forbidding the
diagonal; `GGT/HullSCRelatorSeparation2ApplyLoxGap.lean` records why that clause
was not available. -/
theorem trivial_connector_of_alignedMatch {D : GGT.RelGenSet G Bool}
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
    {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' : G}
    (hx : wordNorm D.base x ≤ eps) (hx' : wordNorm D.base x' ≤ eps)
    (hconn : x * a s ^ e * x' = a s ^ f) (hx'1 : x' = 1) :
    e = f ∧ x = 1 ∧ x' = 1 := by
  have hef : e = f :=
    exponent_eq_of_blockMatch₂ hbase hgeo hdeep hsep he hf hx hx' hconn
  subst hef
  rw [hx'1, mul_one] at hconn
  exact ⟨rfl, mul_eq_right.mp hconn, hx'1⟩

/-- **The aligned case of step (c), closed from the polygon's output.**

The connector relation and the vertex relation the four-gon delivers, the design
clauses, and the conclusion `RelWord.IsPiece` excludes. -/
theorem listVal_conj_of_alignedMatch {D : GGT.RelGenSet G Bool}
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
    {p : List G} {c c' i j : ℕ}
    (hi : i < (relatorWord₂ p (a false) (a true) ms).length)
    (hj : j < (relatorWord₂ p (a false) (a true) ms).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' y : G}
    (hnx : wordNorm D.base x ≤ eps) (hnx' : wordNorm D.base x' ≤ eps)
    (hconn : x * a b ^ e * x' = a b ^ f) (hx'1 : x' = 1)
    (hlet : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)))
    (hlet' : ((relatorWord₂ p (a false) (a true) ms).rotate c')[j]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ f)))
    (hy : y * GGT.OsinComponents.vertex (1 : G)
          ((relatorWord₂ p (a false) (a true) ms).rotate c) i * x'
      = GGT.OsinComponents.vertex (1 : G)
          ((relatorWord₂ p (a false) (a true) ms).rotate c') j) :
    GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c')
      = y * GGT.RelLetter.listVal
          ((relatorWord₂ p (a false) (a true) ms).rotate c) * y⁻¹ := by
  obtain ⟨hef, -, -⟩ :=
    trivial_connector_of_alignedMatch hbase (hgeo b) hdeep hsep he hf
      hnx hnx' hconn hx'1
  rw [hx'1, mul_one] at hy
  have hinj' : ∀ t : Bool,
      Function.Injective (fun n : ℕ => (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  exact listVal_conj_of_alignedTrivial hinj' hnodup hi hj hef hlet hlet' hy

end Close

end HullSC
end GroupApproximation
