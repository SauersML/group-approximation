import GroupApproximation.Analysis.ShulmanFillNormingTailShift

/-!
# Padding a relabelled bounded product back into the original

`shiftSeq c` drops the coordinates below a cut.  This module goes the other
way: `padSeq c` places a sequence over the relabelled models
`shiftModel c = fun m ↦ A (m + c)` at the coordinates from `c` on, with `0`
below.  Padding is a *non-unital* star homomorphism — the unit goes to the
projection onto the late coordinates, which is why the unital `shiftSeq` and
this map are not inverse equivalences — and it is injective, which is all the
MF transfer needs: `HasMFEmbedding` passes backward along it, so the bounded
product of the relabelled models is MF-embeddable whenever the original one is.

The dependent transport is isolated in `castCoord`, the identity homomorphism
read along an equality of indices; every clause about it is proved by `subst`
and nothing downstream rewrites across it.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]

/-- The identity homomorphism read along an equality of indices. -/
def castCoord {a b : ℕ} (h : a = b) : A a →⋆ₙₐ[ℂ] A b :=
  h ▸ (NonUnitalStarAlgHom.id ℂ (A a))

theorem norm_castCoord {a b : ℕ} (h : a = b) (x : A a) :
    ‖castCoord (A := A) h x‖ = ‖x‖ := by
  subst h
  rfl

theorem castCoord_injective {a b : ℕ} (h : a = b) :
    Function.Injective (castCoord (A := A) h) := by
  subst h
  exact fun _ _ hxy ↦ hxy

/-- The padded coordinate function: the relabelled sequence from `c` on,
zero below. -/
def padFun (c : ℕ) (x : StarStrong.BoundedStarSequence (shiftModel (A := A) c))
    (n : ℕ) : A n :=
  if h : c ≤ n then castCoord (Nat.sub_add_cancel h) (x (n - c)) else 0

theorem norm_padFun_le (c : ℕ)
    (x : StarStrong.BoundedStarSequence (shiftModel (A := A) c)) (n : ℕ) :
    ‖padFun c x n‖ ≤ ‖x‖ := by
  by_cases h : c ≤ n
  · rw [padFun, dif_pos h, norm_castCoord]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero x (n - c)
  · rw [padFun, dif_neg h, norm_zero]
    exact norm_nonneg x

/-- **Padding**, as a non-unital star homomorphism of bounded products. -/
def padSeq (c : ℕ) : StarStrong.BoundedStarSequence (shiftModel (A := A) c)
    →⋆ₙₐ[ℂ] StarStrong.BoundedStarSequence A where
  toFun x := ⟨fun n ↦ padFun c x n, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨n, rfl⟩
    exact norm_padFun_le c x n⟩⟩
  map_zero' := by
    refine lp.ext (funext fun n ↦ ?_)
    show padFun c 0 n = 0
    by_cases h : c ≤ n
    · rw [padFun, dif_pos h]
      exact map_zero _
    · rw [padFun, dif_neg h]
  map_add' x y := by
    refine lp.ext (funext fun n ↦ ?_)
    show padFun c (x + y) n = padFun c x n + padFun c y n
    by_cases h : c ≤ n
    · rw [padFun, padFun, padFun, dif_pos h, dif_pos h, dif_pos h, ← map_add]
      rfl
    · rw [padFun, padFun, padFun, dif_neg h, dif_neg h, dif_neg h, add_zero]
  map_mul' x y := by
    refine lp.ext (funext fun n ↦ ?_)
    show padFun c (x * y) n = padFun c x n * padFun c y n
    by_cases h : c ≤ n
    · rw [padFun, padFun, padFun, dif_pos h, dif_pos h, dif_pos h, ← map_mul]
      rfl
    · rw [padFun, padFun, padFun, dif_neg h, dif_neg h, dif_neg h, mul_zero]
  map_smul' z x := by
    refine lp.ext (funext fun n ↦ ?_)
    show padFun c (z • x) n = z • padFun c x n
    by_cases h : c ≤ n
    · rw [padFun, padFun, dif_pos h, dif_pos h, ← map_smul]
      rfl
    · rw [padFun, padFun, dif_neg h, dif_neg h, smul_zero]
  map_star' x := by
    refine lp.ext (funext fun n ↦ ?_)
    show padFun c (star x) n = star (padFun c x n)
    by_cases h : c ≤ n
    · rw [padFun, padFun, dif_pos h, dif_pos h, ← map_star]
      rfl
    · rw [padFun, padFun, dif_neg h, dif_neg h, star_zero]

theorem padSeq_apply (c : ℕ)
    (x : StarStrong.BoundedStarSequence (shiftModel (A := A) c)) (n : ℕ) :
    (padSeq (A := A) c x : ∀ n, A n) n = padFun c x n := rfl

/-- Padding is injective: the coordinate `m + c` recovers the `m`-th entry. -/
theorem padSeq_injective (c : ℕ) :
    Function.Injective (padSeq (A := A) c) := by
  intro x y hxy
  refine lp.ext (funext fun m ↦ ?_)
  have hc : c ≤ m + c := Nat.le_add_left c m
  have hco : padFun c x (m + c) = padFun c y (m + c) := by
    have hval : (padSeq (A := A) c x : ∀ n, A n) (m + c)
        = (padSeq (A := A) c y : ∀ n, A n) (m + c) := by
      rw [hxy]
    rwa [padSeq_apply, padSeq_apply] at hval
  rw [padFun, padFun, dif_pos hc, dif_pos hc] at hco
  have hkey : x (m + c - c) = y (m + c - c) :=
    castCoord_injective (Nat.sub_add_cancel hc) hco
  have hgen : ∀ (k : ℕ), k = m → x k = y k → x m = y m := by
    intro k hk hxk
    subst hk
    exact hxk
  exact hgen (m + c - c) (Nat.add_sub_cancel m c) hkey

/-- MF-embeddability of the bounded product passes to the relabelled one. -/
theorem hasMFEmbedding_of_pad
    (h : HasMFEmbedding (StarStrong.BoundedStarSequence A)) (c : ℕ) :
    HasMFEmbedding (StarStrong.BoundedStarSequence (shiftModel (A := A) c)) :=
  h.of_injective_nonUnitalStarAlgHom (padSeq (A := A) c)
    (padSeq_injective (A := A) c)

end

end ShulmanFill
end GroupApproximation
