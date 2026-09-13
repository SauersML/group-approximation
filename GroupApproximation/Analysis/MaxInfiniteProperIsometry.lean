import GroupApproximation.Analysis.StrictCompressionFromPrinted
import GroupApproximation.Meta.AxiomGuard
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# A proper isometry in `C*_max(G)`, and in every matrix algebra over it

`non_mf_groups_exist.tex`, Proposition `prop:max-infinite` (`\label{prop:max-infinite}`, tex lines 740–749 at
origin/main 68481e4d7):

> Let `G` be a countable group containing a property-(T) subgroup `Γ` and an element `t` with
> `t Γ t⁻¹ ⊊ Γ`.  Then `C*_max(G)` contains a proper isometry.

and the step of its proof at tex lines 768–770:

> so `s` is a proper isometry, and `diag(s,1,…,1)` is one in every matrix algebra over `C*_max(G)`, which is
> therefore not stably finite.

`MaximalCStarPrintedHypotheses.manuscriptMaximalCStarRemarkFromPrintedHypotheses` records the consequences
(failure of Dedekind and stable finiteness, of a faithful trace, of RFD and of MF).  This file states the printed
conclusion literally: an element `s` of `C*_max(G)` with `s* s = 1` and `s s* ≠ 1`, together with the diagonal
amplification `diag(s, 1, …, 1)`, which has the same two properties in `M_{n+1}(C*_max(G))` for every `n`.  The
isometry is the printed `s = P u* + (1 - q)` (`ProperProjectionCompression.isometry`) of the strict Kazhdan
compression built from the printed hypotheses alone.  The statement drops the countability of `G`, so it is more
general than the printed one.
-/

namespace GroupApproximation
namespace MaxInfiniteProperIsometry

universe u v

/-- The diagonal entries `(s, 1, …, 1)` of the printed amplification `diag(s,1,…,1)` in rank `n + 1`. -/
def diagEntries {A : Type v} [One A] (s : A) (n : ℕ) : Fin (n + 1) → A :=
  fun i ↦ if i = 0 then s else 1

/-- The printed matrix `diag(s,1,…,1)` in `M_{n+1}(A)`. -/
def diagAmplification {A : Type v} [Ring A] (s : A) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  Matrix.diagonal (diagEntries s n)

/-- `diag(s,1,…,1)` is an isometry whenever `s` is. -/
theorem star_diagAmplification_mul_self {A : Type v} [Ring A] [StarRing A] {s : A}
    (hs : star s * s = 1) (n : ℕ) :
    star (diagAmplification s n) * diagAmplification s n = 1 := by
  have hentries :
      (fun i ↦ (star (diagEntries s n)) i * diagEntries s n i) = fun _ ↦ (1 : A) := by
    funext i
    by_cases hi : i = 0
    · simpa [diagEntries, hi] using hs
    · simp [diagEntries, hi]
  rw [Matrix.star_eq_conjTranspose, diagAmplification, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, hentries, Matrix.diagonal_one]

/-- `diag(s,1,…,1)` is not a coisometry whenever `s` is not: its `(0,0)` entry of `M M*` is `s s*`. -/
theorem diagAmplification_mul_star_ne_one {A : Type v} [Ring A] [StarRing A] {s : A}
    (hs : s * star s ≠ 1) (n : ℕ) :
    diagAmplification s n * star (diagAmplification s n) ≠ 1 := by
  intro h
  apply hs
  have h00 : (diagAmplification s n * star (diagAmplification s n)) 0 0 =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) 0 0 := by
    rw [h]
  rw [Matrix.star_eq_conjTranspose, diagAmplification, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h00
  simpa [diagEntries] using h00

/-- **`prop:max-infinite`, the proper isometry, as printed.**

For every group `G`, every subgroup `Γ` with property (T) and every `t` with `t Γ t⁻¹ ⊊ Γ`, the maximal group
`C*`-algebra contains `s` with `s* s = 1` and `s s* ≠ 1` (tex lines 742–743), and for every `n` the matrix
`diag(s,1,…,1)` in `M_{n+1}(C*_max(G))` has the same two properties (tex lines 768–770). -/
def PrintedMaxInfiniteProperIsometry : Prop :=
  ∀ (G : Type u) [Group G] (Γ : Subgroup G) (t : G),
    HasKazhdanPropertyT.{u, u} ↥Γ →
    Γ.map (MulAut.conj t).toMonoidHom < Γ →
    ∃ s : MaximalGroupCStar G,
      star s * s = 1 ∧ s * star s ≠ 1 ∧
        ∀ n : ℕ, star (diagAmplification s n) * diagAmplification s n = 1 ∧
          diagAmplification s n * star (diagAmplification s n) ≠ 1

/-- **`prop:max-infinite`, the proper isometry, closed.**  The isometry is the printed `s = P u* + (1 - q)` of the
strict Kazhdan compression that `MaximalCStarPrintedHypotheses.exists_strictKazhdanCompression` builds from the
printed hypotheses. -/
theorem manuscriptMaxInfiniteProperIsometry : PrintedMaxInfiniteProperIsometry.{u} := by
  intro G _ Γ t hT hlt
  obtain ⟨D, -⟩ := MaximalCStarPrintedHypotheses.exists_strictKazhdanCompression Γ t hT hlt
  refine ⟨D.toProperProjectionCompression.isometry,
    D.toProperProjectionCompression.star_isometry_mul_isometry,
    D.toProperProjectionCompression.isometry_mul_star_ne_one, fun n ↦ ⟨?_, ?_⟩⟩
  · exact star_diagAmplification_mul_self
      D.toProperProjectionCompression.star_isometry_mul_isometry n
  · exact diagAmplification_mul_star_ne_one
      D.toProperProjectionCompression.isometry_mul_star_ne_one n

end MaxInfiniteProperIsometry
end GroupApproximation

open GroupApproximation

#audit_axioms MaxInfiniteProperIsometry.star_diagAmplification_mul_self
#audit_axioms MaxInfiniteProperIsometry.diagAmplification_mul_star_ne_one
#audit_closed_axioms MaxInfiniteProperIsometry.manuscriptMaxInfiniteProperIsometry
