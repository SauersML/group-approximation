import GroupApproximation.GGT.HullSCRelatorSeparation2AlignedClose

/-!
# The rigidity in the currency the polygon actually pays in

`GGT.OsinComponents.exists_two_block_conj_of_rot` delivers its two gaps as
**members of `D.relBall lam (C · 4)`**, not as elements with a word-norm bound.
That is the better currency, and it shortens the chain rather than lengthening
it: the design's separation and diagonal clauses are themselves stated over the
relative ball, so a gap that arrives in the ball can be fed to them directly.

What drops out is the whole conversion apparatus.  The word-norm form of the
rigidity spends `hgeo` twice -- once to place the conjugators in the subgroup,
once more inside `HullSC.mem_relBall_of_wordNorm_le` to turn that plus the norm
bound into ball membership -- and it does so only to reach the ball.  Given the
ball, neither step is needed, and `exponent_eq_of_blockMatch_ball` is three
lines with no geometric input at all.

The isolated-component bound does not leave the chain: it is the first binder of
the packaged theorem, which is where it belongs.  What leaves is this chain's own
use of it.  `GGT/HullSCRelatorSeparation2Rigidity.lean` stays for consumers that
hold a norm bound rather than ball membership; nothing here supersedes it.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Ball

variable {G : Type u} [Group G]

/-- **Matched blocks carry equal exponents**, from ball membership alone. -/
theorem exponent_eq_of_blockMatch_ball {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} {s : Bool}
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {i j : ℕ} (hi : i ∈ ms) (hj : j ∈ ms) {x x' : G}
    (hx : x ∈ D.relBall s eps) (hx' : x' ∈ D.relBall s eps)
    (heq : x * a s ^ i * x' = a s ^ j) : i = j := by
  by_contra hij
  exact (hsep i hi j hj hij s x hx x' hx').1 heq

/-- **The mirrored form**, likewise. -/
theorem exponent_eq_of_mirroredBlockMatch_ball {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} {s : Bool}
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {i j : ℕ} (hi : i ∈ ms) (hj : j ∈ ms) {x x' : G}
    (hx : x ∈ D.relBall s eps) (hx' : x' ∈ D.relBall s eps)
    (heq : x * a s ^ i * x' = (a s ^ j)⁻¹) : i = j := by
  by_contra hij
  exact (hsep i hi j hj hij s x hx x' hx').2 heq

/-- **At a matched block of the aligned case the connectors are trivial**, from
ball membership alone: the exponents agree, the relation is the diagonal, and
the design forbids it for a nontrivial left connector. -/
theorem trivial_connector_of_alignedMatch_ball {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} {s : Bool}
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdiag : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * a t ^ i * x' ≠ a t ^ i)
    {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' : G}
    (hx : x ∈ D.relBall s eps) (hx' : x' ∈ D.relBall s eps)
    (hconn : x * a s ^ e * x' = a s ^ f) : e = f ∧ x = 1 ∧ x' = 1 := by
  have hef : e = f := exponent_eq_of_blockMatch_ball hsep he hf hx hx' hconn
  subst hef
  have hx1 : x = 1 := by
    by_contra hne
    exact hdiag e he s x hx x' hx' hne hconn
  refine ⟨rfl, hx1, ?_⟩
  rw [hx1, one_mul] at hconn
  exact mul_eq_left.mp hconn

/-- **The aligned case, closed from the packaged theorem's own output.**

The gaps arrive in the relative ball, the design makes them trivial, and the
join turns the vertex relation into the identity `RelWord.IsPiece` excludes. -/
theorem listVal_conj_of_alignedMatch_ball {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdiag : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * a t ^ i * x' ≠ a t ^ i)
    {p : List G} {c c' i j : ℕ}
    (hi : i < (relatorWord₂ p (a false) (a true) ms).length)
    (hj : j < (relatorWord₂ p (a false) (a true) ms).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' y : G}
    (hx : x ∈ D.relBall b eps) (hx' : x' ∈ D.relBall b eps)
    (hconn : x * a b ^ e * x' = a b ^ f)
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
  obtain ⟨hef, -, hx'1⟩ :=
    trivial_connector_of_alignedMatch_ball hsep hdiag he hf hx hx' hconn
  rw [hx'1, mul_one] at hy
  have hinj' : ∀ t : Bool,
      Function.Injective (fun n : ℕ => (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  exact listVal_conj_of_alignedTrivial hinj' hnodup hi hj hef hlet hlet' hy

end Ball

end HullSC
end GroupApproximation
