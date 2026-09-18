import GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoid.OperatorPath
import GroupApproximation.Meta.AxiomGuard

/-!
# Concatenating operator paths, and adding a fixed summand

## The proof route

* `OpPath.trans`: the path is `concatPath P Q`.  On `s ≤ 1/2` it agrees pointwise with
  `P (c(2s))` (`concatPath_toFun_of_le_half`), and on `s ≥ 1/2` with `Q (c(2s - 1))`
  (`concatPath_toFun_of_half_le`).  So each value is a Kasparov operator.  For continuity at
  `t`, take `δ₁` for `P` at `c(2t)` and `δ₂` for `Q` at `c(2t - 1)`, both for `ε/2`, and let
  `δ = min δ₁ δ₂ / 2`.  If `|s - t| < δ` then `|2s - 2t| < min δ₁ δ₂`, and the clamp is
  `1`-Lipschitz.  The difference of the two values is, pointwise, a `P`-difference plus a
  `Q`-difference (`abel`), bounded by `ε/2 + ε/2`.
* `OpPath.prodMap_right`: `s ↦ P s ⊞ K`, bounded by `ε + 0` (`IsBoundedBy.prodMap`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KKMonoidLane

open HilbertModule

universe u v w w'

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {E : CStarModule.{v, w} B} {γ : Adjointable E E} {ρ : A → Adjointable E E}

omit [PartialOrder B] [StarOrderedRing B] in
theorem concatPath_toFun_of_le_half {P Q : ℝ → Adjointable E E}
    (hPQ : ∀ x, (Q 0).toFun x = (P 1).toFun x) {s : ℝ} (hs : s ≤ 1 / 2) (x : E.carrier) :
    (P (clamp01 (2 * s))).toFun x = (concatPath P Q s).toFun x := by
  have h2 : 2 * s - 1 ≤ 0 := by linarith
  rw [concatPath_toFun, clamp01_of_nonpos h2, hPQ x]
  abel

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.concatPath_toFun_of_le_half

omit [PartialOrder B] [StarOrderedRing B] in
theorem concatPath_toFun_of_half_le (P Q : ℝ → Adjointable E E) {s : ℝ} (hs : 1 / 2 ≤ s)
    (x : E.carrier) :
    (Q (clamp01 (2 * s - 1))).toFun x = (concatPath P Q s).toFun x := by
  have h2 : 1 ≤ 2 * s := by linarith
  rw [concatPath_toFun, clamp01_of_one_le h2]
  abel

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.concatPath_toFun_of_half_le

theorem OpPath.trans {F G H : Adjointable E E} (hp : OpPath E γ ρ F G)
    (hq : OpPath E γ ρ G H) : OpPath E γ ρ F H := by
  obtain ⟨P, hP, hcP, p0, p1⟩ := hp
  obtain ⟨Q, hQ, hcQ, q0, q1⟩ := hq
  have hPQ : ∀ x, (Q 0).toFun x = (P 1).toFun x := fun x => (q0 x).trans (p1 x).symm
  refine ⟨concatPath P Q, fun s => ?_, ?_, fun x => ?_, fun x => ?_⟩
  · rcases le_total s (1 / 2) with hs | hs
    · exact (hP _).congr (concatPath_toFun_of_le_half hPQ hs)
    · exact (hQ _).congr (concatPath_toFun_of_half_le P Q hs)
  · intro t ε hε
    obtain ⟨δ₁, hδ₁, hb₁⟩ := hcP (clamp01 (2 * t)) (ε / 2) (half_pos hε)
    obtain ⟨δ₂, hδ₂, hb₂⟩ := hcQ (clamp01 (2 * t - 1)) (ε / 2) (half_pos hε)
    refine ⟨min δ₁ δ₂ / 2, half_pos (lt_min hδ₁ hδ₂), fun s hs => ?_⟩
    have h2 : |2 * s - 2 * t| < min δ₁ δ₂ := by
      have hmul : 2 * s - 2 * t = 2 * (s - t) := by ring
      rw [hmul, abs_mul, abs_two]
      linarith
    have hP' : |clamp01 (2 * s) - clamp01 (2 * t)| < δ₁ :=
      lt_of_le_of_lt (abs_clamp01_sub_le _ _) (lt_of_lt_of_le h2 (min_le_left _ _))
    have hQ' : |clamp01 (2 * s - 1) - clamp01 (2 * t - 1)| < δ₂ := by
      have h3 := abs_clamp01_sub_le (2 * s - 1) (2 * t - 1)
      rw [show 2 * s - 1 - (2 * t - 1) = 2 * s - 2 * t by ring] at h3
      exact lt_of_le_of_lt h3 (lt_of_lt_of_le h2 (min_le_right _ _))
    have hsum := Adjointable.IsBoundedBy.add (hb₁ _ hP') (hb₂ _ hQ')
    refine Adjointable.IsBoundedBy.mono (Adjointable.IsBoundedBy.congr (fun x => ?_) hsum)
      (le_of_eq (add_halves ε))
    show (P (clamp01 (2 * s))).toFun x - (P (clamp01 (2 * t))).toFun x
        + ((Q (clamp01 (2 * s - 1))).toFun x - (Q (clamp01 (2 * t - 1))).toFun x)
      = (concatPath P Q s).toFun x - (concatPath P Q t).toFun x
    rw [concatPath_toFun, concatPath_toFun]
    abel
  · rw [← concatPath_toFun_of_le_half hPQ (s := 0) (by norm_num) x,
      clamp01_of_nonpos (by norm_num : (2 : ℝ) * 0 ≤ 0)]
    exact p0 x
  · rw [← concatPath_toFun_of_half_le P Q (s := 1) (by norm_num) x,
      clamp01_of_one_le (by norm_num : (1 : ℝ) ≤ 2 * 1 - 1)]
    exact q1 x

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.OpPath.trans

/-- Adding a fixed Kasparov operator as a second summand carries paths to paths. -/
theorem OpPath.prodMap_right {E' : CStarModule.{v, w'} B} {γ' : Adjointable E' E'}
    {ρ' : A → Adjointable E' E'} {F G : Adjointable E E} {K : Adjointable E' E'}
    (hp : OpPath E γ ρ F G) (hK : IsKasparovOp E' γ' ρ' K) :
    OpPath (prod E E') (Adjointable.prodMap γ γ') (fun a => Adjointable.prodMap (ρ a) (ρ' a))
      (Adjointable.prodMap F K) (Adjointable.prodMap G K) := by
  obtain ⟨P, hP, hc, h0, h1⟩ := hp
  refine ⟨fun s => Adjointable.prodMap (P s) K, fun s => (hP s).prodMap hK, ?_,
    fun p => ?_, fun p => ?_⟩
  · intro t ε hε
    obtain ⟨δ, hδ, hb⟩ := hc t ε hε
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have hsum := Adjointable.IsBoundedBy.prodMap (hb s hs)
      (isBoundedBy_sub_self K (le_refl (0 : ℝ))) hε.le (le_refl (0 : ℝ))
    exact Adjointable.IsBoundedBy.mono (Adjointable.IsBoundedBy.congr (fun _ => rfl) hsum)
      (le_of_eq (add_zero ε))
  · exact Prod.ext (h0 p.1) rfl
  · exact Prod.ext (h1 p.1) rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.OpPath.prodMap_right

end KKMonoidLane
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
