import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftFaithful
import GroupApproximation.Analysis.ShulmanFillNormingTailAsymptotic

/-!
# The paired doubling, for tail lifts

`ShulmanFill.StarStrongAsymptoticLift.doubleLR` builds, from lifts of `ρ₁` and
`ρ₂` into `𝒟`, a lift of the paired representation `ρ₁ ⊕ ρ₂` into the doubled
`𝒟`.  This module rebuilds it for `StarStrongTailLift`, which is the vocabulary
the repaired binder is stated in
(`Analysis/ShulmanFillNormingTailPrinted`).

Nothing about the *sequences* changes, and none of it is rebuilt:
`doubledPairSeq` and its algebraic identities, its norm bound, its membership in
`𝒟` and its `*`-strong limit all come from
`Analysis/ShulmanFillNormingExistentialLiftPair` unchanged.  What changes is the
five defect fields and the lift field.

* **The defects.**  Each doubled defect *is* the paired sequence of the two
  original defects, so at every coordinate its norm is at most the larger of
  theirs.  `TailNull.doubledPair` is that observation, and the cut of the
  doubled lift is the pointwise maximum of the two cuts --- `TailNull.mono_cut`
  says a larger cut asks for less, so both legs' defects survive being read past
  it.
* **The lift.**  With the pointwise clause there is nothing to identify
  exactly.  The doubled `*`-strong limit is the block diagonal of the two
  limits, `hBlockOp` is isometric because it is injective
  (`hBlockOp_injective`), and the block diagonal of a pair is bounded by the
  larger of the pair, so the two convergences give the doubled one.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u

section TailPair

/-! ## Tail vanishing under pairing

The binders are the ones `Analysis/ShulmanFillNormingExistentialLiftPair`
declares for its sequence section: the doubled model is `M₂` over the
coefficients, and its C-star structure is reached through the Loewner order, so
`PartialOrder` and `StarOrderedRing` have to be in scope wherever
`doubledPairSeq` is mentioned. -/

section CutMono

-- `TailNull` is polymorphic and `StarStrongTailLift`'s family lives in `Type u`,
-- so this lemma has to be stated there too; the doubling below is `Type 0` only,
-- because `doubledPairSeq` is.
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]

/-- A larger cut asks for less. -/
theorem TailNull.mono_cut {cut cut' : ℕ → ℕ}
    {X : ℕ → StarStrong.BoundedStarSequence A} (h : TailNull cut X)
    (hc : ∀ t, cut t ≤ cut' t) : TailNull cut' X := by
  intro ε hε
  exact (h ε hε).mono fun t ht n hn ↦ ht n (le_trans (hc t) hn)

end CutMono

section PairedTail

variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
variable [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]

/-- **The paired sequence of two tail-null families is tail-null.**  At every
coordinate the paired sequence is the block diagonal of the two, whose norm is
the larger of theirs. -/
theorem TailNull.doubledPair {cut : ℕ → ℕ}
    {X Y : ℕ → StarStrong.BoundedStarSequence A}
    (hX : TailNull cut X) (hY : TailNull cut Y) :
    TailNull cut (fun t ↦ doubledPairSeq (A := A) (X t) (Y t)) := by
  intro ε hε
  filter_upwards [hX ε hε, hY ε hε] with t htX htY n hn
  have hcoord : ‖doubledPairSeq (A := A) (X t) (Y t) n‖
      ≤ max ‖X t n‖ ‖Y t n‖ := by
    rw [doubledPairSeq_apply]
    exact norm_diagonalPairHom2_le ((X t n, Y t n) : A n × A n)
  exact hcoord.trans (max_le (htX n hn) (htY n hn))

end PairedTail

section BlockNorm

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- **The block diagonal is bounded by the larger of its entries**, at the
level of operators.  `hBlockOp` is injective, hence isometric, so this is
`norm_diagonalPairHom2_le` transported. -/
theorem norm_hBlockOp_diagonalPairHom2_le (S T : H →L[ℂ] H) :
    ‖hBlockOp (E := H) (n := 2)
        (diagonalPairHom2 ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H)))‖
      ≤ max ‖S‖ ‖T‖ := by
  have hiso : Isometry (hBlockOpHom (E := H) (n := 2)) :=
    NonUnitalStarAlgHom.isometry
      (hBlockOpHom (E := H) (n := 2)).toNonUnitalStarAlgHom hBlockOp_injective
  have hnorm : ‖hBlockOp (E := H) (n := 2)
      (diagonalPairHom2 ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H)))‖
      = ‖diagonalPairHom2 ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H))‖ :=
    hiso.norm_map_of_map_zero (map_zero _) _
  rw [hnorm]
  exact norm_diagonalPairHom2_le _

end BlockNorm

section Lift

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
variable [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
variable [∀ n, Nontrivial (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}

namespace StarStrongTailLift

variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {B : Type} [CStarAlgebra B] {ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- **The paired doubling of two tail lifts.**  The cut is the pointwise
maximum of the two cuts. -/
def doubleLR (φ₁ : StarStrongTailLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongTailLift ι hnorm hone ρ₂) :
    StarStrongTailLift (doubledIota ι) (doubled_norm_le ι)
      (doubled_hone ι hone) (pairRep ρ₁ ρ₂) where
  toFun t b := doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b)
  cut t := max (φ₁.cut t) (φ₂.cut t)
  mem t b := doubledPairSeq_mem ι hnorm hone (φ₁.toFun t b) (φ₂.toFun t b)
    (φ₁.mem t b) (φ₂.mem t b)
  norm_le t b := (norm_doubledPairSeq_le _ _).trans
    (max_le (φ₁.norm_le t b) (φ₂.norm_le t b))
  tail_add b c := by
    have hfun : (fun t ↦ doubledPairSeq (A := A)
          (φ₁.toFun t (b + c)) (φ₂.toFun t (b + c))
        - doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b)
        - doubledPairSeq (A := A) (φ₁.toFun t c) (φ₂.toFun t c))
        = fun t ↦ doubledPairSeq (A := A)
            (φ₁.toFun t (b + c) - φ₁.toFun t b - φ₁.toFun t c)
            (φ₂.toFun t (b + c) - φ₂.toFun t b - φ₂.toFun t c) := by
      funext t
      rw [doubledPairSeq_sub, doubledPairSeq_sub]
    rw [hfun]
    exact TailNull.doubledPair
      ((φ₁.tail_add b c).mono_cut fun t ↦ le_max_left _ _)
      ((φ₂.tail_add b c).mono_cut fun t ↦ le_max_right _ _)
  tail_smul z b := by
    have hfun : (fun t ↦ doubledPairSeq (A := A)
          (φ₁.toFun t (z • b)) (φ₂.toFun t (z • b))
        - z • doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b))
        = fun t ↦ doubledPairSeq (A := A)
            (φ₁.toFun t (z • b) - z • φ₁.toFun t b)
            (φ₂.toFun t (z • b) - z • φ₂.toFun t b) := by
      funext t
      have hsm := map_smul (doubledPairSeqHom (A := A)) z
        ((φ₁.toFun t b, φ₂.toFun t b) :
          StarStrong.BoundedStarSequence A × StarStrong.BoundedStarSequence A)
      rw [show z • ((φ₁.toFun t b, φ₂.toFun t b) :
            StarStrong.BoundedStarSequence A × StarStrong.BoundedStarSequence A)
          = (z • φ₁.toFun t b, z • φ₂.toFun t b) from rfl] at hsm
      simp only [doubledPairSeqHom_apply] at hsm
      rw [← hsm, ← doubledPairSeq_sub]
    rw [hfun]
    exact TailNull.doubledPair
      ((φ₁.tail_smul z b).mono_cut fun t ↦ le_max_left _ _)
      ((φ₂.tail_smul z b).mono_cut fun t ↦ le_max_right _ _)
  tail_mul b c := by
    have hfun : (fun t ↦ doubledPairSeq (A := A)
          (φ₁.toFun t (b * c)) (φ₂.toFun t (b * c))
        - doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b)
          * doubledPairSeq (A := A) (φ₁.toFun t c) (φ₂.toFun t c))
        = fun t ↦ doubledPairSeq (A := A)
            (φ₁.toFun t (b * c) - φ₁.toFun t b * φ₁.toFun t c)
            (φ₂.toFun t (b * c) - φ₂.toFun t b * φ₂.toFun t c) := by
      funext t
      rw [doubledPairSeq_sub, doubledPairSeq_mul]
    rw [hfun]
    exact TailNull.doubledPair
      ((φ₁.tail_mul b c).mono_cut fun t ↦ le_max_left _ _)
      ((φ₂.tail_mul b c).mono_cut fun t ↦ le_max_right _ _)
  tail_star b := by
    have hfun : (fun t ↦ doubledPairSeq (A := A)
          (φ₁.toFun t (star b)) (φ₂.toFun t (star b))
        - star (doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b)))
        = fun t ↦ doubledPairSeq (A := A)
            (φ₁.toFun t (star b) - star (φ₁.toFun t b))
            (φ₂.toFun t (star b) - star (φ₂.toFun t b)) := by
      funext t
      rw [doubledPairSeq_sub, doubledPairSeq_star]
    rw [hfun]
    exact TailNull.doubledPair
      ((φ₁.tail_star b).mono_cut fun t ↦ le_max_left _ _)
      ((φ₂.tail_star b).mono_cut fun t ↦ le_max_right _ _)
  tail_one := by
    have hfun : (fun t ↦ doubledPairSeq (A := A)
          (φ₁.toFun t 1) (φ₂.toFun t 1) - 1)
        = fun t ↦ doubledPairSeq (A := A)
            (φ₁.toFun t 1 - 1) (φ₂.toFun t 1 - 1) := by
      funext t
      rw [doubledPairSeq_sub, doubledPairSeq_one]
    rw [hfun]
    exact TailNull.doubledPair
      (φ₁.tail_one.mono_cut fun t ↦ le_max_left _ _)
      (φ₂.tail_one.mono_cut fun t ↦ le_max_right _ _)
  tendsto_lift b := by
    have hid : ∀ t : ℕ, StarStrong.starStrongLimitHom (doubledIota ι)
        (doubled_norm_le ι) (doubled_hone ι hone)
        ⟨doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b),
          doubledPairSeq_mem ι hnorm hone (φ₁.toFun t b) (φ₂.toFun t b)
            (φ₁.mem t b) (φ₂.mem t b)⟩
        = hBlockOp (diagonalPairHom2
            ((StarStrong.starStrongLimitHom ι hnorm hone
                ⟨φ₁.toFun t b, φ₁.mem t b⟩,
              StarStrong.starStrongLimitHom ι hnorm hone
                ⟨φ₂.toFun t b, φ₂.mem t b⟩) :
              (H →L[ℂ] H) × (H →L[ℂ] H))) := by
      intro t
      refine StarStrong.starStrongLimit_eq (doubledIota ι) (doubled_norm_le ι)
        (doubled_hone ι hone) _
        (isStarStrongLimit_doubledPairSeq ι (φ₁.toFun t b) (φ₂.toFun t b) ?_ ?_)
      · exact StarStrong.starStrongLimit_spec ι hnorm hone
          ⟨φ₁.toFun t b, φ₁.mem t b⟩
      · exact StarStrong.starStrongLimit_spec ι hnorm hone
          ⟨φ₂.toFun t b, φ₂.mem t b⟩
    have hmax : Tendsto (fun t ↦ max
        ‖StarStrong.starStrongLimitHom ι hnorm hone
          ⟨φ₁.toFun t b, φ₁.mem t b⟩ - ρ₁ b‖
        ‖StarStrong.starStrongLimitHom ι hnorm hone
          ⟨φ₂.toFun t b, φ₂.mem t b⟩ - ρ₂ b‖) atTop (𝓝 0) := by
      have h := (φ₁.tendsto_lift b).max (φ₂.tendsto_lift b)
      rwa [max_self] at h
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun t ↦ ?_) hmax
    rw [hid t, pairRep_apply]
    have hsub : hBlockOp (E := H) (n := 2) (diagonalPairHom2
          ((StarStrong.starStrongLimitHom ι hnorm hone
              ⟨φ₁.toFun t b, φ₁.mem t b⟩,
            StarStrong.starStrongLimitHom ι hnorm hone
              ⟨φ₂.toFun t b, φ₂.mem t b⟩) :
            (H →L[ℂ] H) × (H →L[ℂ] H)))
        - hBlockOp (E := H) (n := 2) (diagonalPairHom2
            ((ρ₁ b, ρ₂ b) : (H →L[ℂ] H) × (H →L[ℂ] H)))
        = hBlockOp (E := H) (n := 2) (diagonalPairHom2
            ((StarStrong.starStrongLimitHom ι hnorm hone
                ⟨φ₁.toFun t b, φ₁.mem t b⟩ - ρ₁ b,
              StarStrong.starStrongLimitHom ι hnorm hone
                ⟨φ₂.toFun t b, φ₂.mem t b⟩ - ρ₂ b) :
              (H →L[ℂ] H) × (H →L[ℂ] H))) := by
      simp only [← hBlockOpHom_apply]
      rw [← map_sub (hBlockOpHom (E := H) (n := 2)), ← map_sub diagonalPairHom2]
      rfl
    rw [hsub]
    exact norm_hBlockOp_diagonalPairHom2_le _ _

end StarStrongTailLift

end Lift

end TailPair

end

end ShulmanFill
end GroupApproximation
