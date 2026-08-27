import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv

/-!
# The corner-embedding remark: MF algebras are exactly the algebras embedding
in the universal norm matrix corona

`mf_recognition_complexity.tex`, `\section{HNN extensions with a corona
conjugator}` (`sec:hnn`), the remark following the tracial-MF-realization
definition:

Sentence `49af36bf9b2e`: "To embed an arbitrary norm matrix corona
`Q_{\mathbf d}` in `∏_kM_k(ℂ)/⊕_kM_k(ℂ)`, choose a strictly increasing
sequence `(m_n)` with `m_n≥d_n`, embed `M_{d_n}(ℂ)` as a corner of
`M_{m_n}(ℂ)`, and put zero in the unused coordinates. The resulting map on
reduced products is an isometric `*`-homomorphism, so the MF algebras of
Section `sec:prelim` are exactly the separable `C^*`-algebras that embed in
the latter corona, as in `[BK, Shulman]`."

## Division of labour with the existing development

The manuscript's construction has two parts. The first -- realizing an
*arbitrary* positive dimension sequence `(d_n)` as a corner of *some*
strictly increasing sequence `(m_n)` -- is already unconditionally proved as
`MFAlgebraDimension.hasMFEmbedding_iff` / `MFAlgebraDimension.isMFAlgebra_iff`
(`Analysis/MFAlgebraDimensionNormalization.lean`): the corner map there is
`MFAlgebraDimension.cornerCoronaHom`, an injective, norm-preserving,
nonunital `⋆`-homomorphism onto the cumulative block model
`increasingBlockModel`, whose cardinalities strictly increase. Since
`IsMFAlgebra` is *defined* through `HasMFEmbedding`, which already bakes in
that strict monotonicity, every MF algebra already comes with such an
embedding into a corona over *some* strictly increasing sequence.

What remains -- "put zero in the unused coordinates" -- is the second part:
a strictly increasing sequence `(m_n)` need not enumerate *every* positive
integer, so a corona over `(m_n)` need not literally be
`∏_kM_k(ℂ)/⊕_kM_k(ℂ)` (the corona with dimension exactly `k` at position
`k`, here `naturalFiniteModel (k+1)`, `k=0,1,2,…`). This file supplies that
missing spread: given a strictly increasing dimension sequence `(m_n)`, the
matrix at target position `k` is placed there when `k+1` happens to equal
some `m_n` (reindexed to the literal basis `Fin (k+1)`), and is zero
otherwise. `spreadCoronaHom` bundles the induced map on norm matrix coronas
as an injective nonunital `⋆`-homomorphism, and `isNull_spreadSeq_iff` is
the exact cofinite-nullity computation that makes it isometric in the sense
that matters for the corona quotient (nullity, hence injectivity, is
reflected exactly).

`isMFAlgebra_iff_embeds_universalCorona` is the closed statement of the
printed remark: `IsMFAlgebra A` holds exactly when `A` is separable and
embeds, by an injective nonunital `⋆`-homomorphism, in the single fixed
corona `∏_kM_k(ℂ)/⊕_kM_k(ℂ)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace CoronaEmbeddingRemark

open Filter Matrix Classical
open scoped Matrix.Norms.L2Operator
open MFAlgebraDimension (normMatrixCStarCoronaMk_smul)

universe u

noncomputable section

variable (X : ℕ → FiniteModel)

/-! ## Placing one finite matrix coordinate at a fixed target position -/

/-- The value placed by the spread map at target position `k`: if `k + 1`
happens to be the cardinality of some source coordinate `X n`, reindex that
coordinate's matrix to the literal basis `Fin (k + 1)` and place it there;
otherwise place zero. The witness `n` is unique whenever
`Fintype.card ∘ X` is strictly increasing, which is what makes this
well behaved below. -/
def spreadCoord (f : ∀ n, Matrix (X n) (X n) ℂ) (k : ℕ) :
    Matrix (naturalFiniteModel (k + 1)) (naturalFiniteModel (k + 1)) ℂ :=
  if hex : ∃ n, Fintype.card (X n) = k + 1 then
    matrixReindexStarAlgEquiv
      ((Fintype.equivFin (X hex.choose)).trans (finCongr hex.choose_spec))
      (f hex.choose)
  else 0

set_option maxHeartbeats 800000 in
/-- **The one place `spreadCoord`'s `dite` is unfolded on the hit branch.**
Every other lemma about `spreadCoord` at a hit position is proved by
rewriting with this (and `spreadCoord_of_miss` on the miss branch), never by
unfolding `spreadCoord` itself again -- repeated unfolding against the
classical decidability instance is what makes the naive approach time out. -/
theorem spreadCoord_of_hit
    (f : ∀ n, Matrix (X n) (X n) ℂ) {k : ℕ}
    (hex : ∃ n, Fintype.card (X n) = k + 1) :
    spreadCoord X f k =
      matrixReindexStarAlgEquiv
        ((Fintype.equivFin (X hex.choose)).trans (finCongr hex.choose_spec))
        (f hex.choose) :=
  dif_pos hex

set_option maxHeartbeats 800000 in
/-- **The one place `spreadCoord`'s `dite` is unfolded on the miss branch.** -/
theorem spreadCoord_of_miss
    (f : ∀ n, Matrix (X n) (X n) ℂ) {k : ℕ}
    (hex : ¬ ∃ n, Fintype.card (X n) = k + 1) :
    spreadCoord X f k = 0 :=
  dif_neg hex

theorem spreadCoord_of_not_hit
    (f : ∀ n, Matrix (X n) (X n) ℂ) {k : ℕ}
    (hex : ¬ ∃ n, Fintype.card (X n) = k + 1) :
    spreadCoord X f k = 0 :=
  spreadCoord_of_miss X f hex

/-- The norm of the spread value at a hit position is exactly the norm of
the source coordinate, once the source dimension sequence is strictly
increasing (so the witness index is unique). -/
theorem norm_spreadCoord_of_card_eq
    (hmono : StrictMono (fun n ↦ Fintype.card (X n)))
    (f : ∀ n, Matrix (X n) (X n) ℂ) {n k : ℕ}
    (h : Fintype.card (X n) = k + 1) :
    ‖spreadCoord X f k‖ = ‖f n‖ := by
  have hex : ∃ n', Fintype.card (X n') = k + 1 := ⟨n, h⟩
  have hchoose : hex.choose = n := hmono.injective (hex.choose_spec.trans h.symm)
  rw [spreadCoord_of_hit X f hex, norm_matrixReindexStarAlgEquiv, hchoose]

/-- The spread value at any position is bounded by any uniform bound on the
source coordinates, with no monotonicity hypothesis: this is what is needed
to know the spread sequence stays bounded. -/
theorem norm_spreadCoord_le
    (f : ∀ n, Matrix (X n) (X n) ℂ) (C : ℝ) (hC : ∀ n, ‖f n‖ ≤ C) (hC0 : 0 ≤ C)
    (k : ℕ) : ‖spreadCoord X f k‖ ≤ C := by
  by_cases hex : ∃ n, Fintype.card (X n) = k + 1
  · rw [spreadCoord_of_hit X f hex, norm_matrixReindexStarAlgEquiv]
    exact hC _
  · rw [spreadCoord_of_miss X f hex, norm_zero]
    exact hC0

theorem spreadCoord_zero (k : ℕ) :
    spreadCoord X (0 : ∀ n, Matrix (X n) (X n) ℂ) k = 0 := by
  by_cases hex : ∃ n, Fintype.card (X n) = k + 1
  · rw [spreadCoord_of_hit X _ hex, Pi.zero_apply, map_zero]
  · exact spreadCoord_of_miss X _ hex

theorem spreadCoord_add (f g : ∀ n, Matrix (X n) (X n) ℂ) (k : ℕ) :
    spreadCoord X (f + g) k = spreadCoord X f k + spreadCoord X g k := by
  by_cases hex : ∃ n, Fintype.card (X n) = k + 1
  · rw [spreadCoord_of_hit X (f + g) hex, spreadCoord_of_hit X f hex,
      spreadCoord_of_hit X g hex, Pi.add_apply, map_add]
  · rw [spreadCoord_of_miss X _ hex, spreadCoord_of_miss X f hex,
      spreadCoord_of_miss X g hex, add_zero]

theorem spreadCoord_sub (f g : ∀ n, Matrix (X n) (X n) ℂ) (k : ℕ) :
    spreadCoord X (f - g) k = spreadCoord X f k - spreadCoord X g k := by
  by_cases hex : ∃ n, Fintype.card (X n) = k + 1
  · rw [spreadCoord_of_hit X (f - g) hex, spreadCoord_of_hit X f hex,
      spreadCoord_of_hit X g hex, Pi.sub_apply, map_sub]
  · rw [spreadCoord_of_miss X _ hex, spreadCoord_of_miss X f hex,
      spreadCoord_of_miss X g hex, sub_zero]

theorem spreadCoord_smul (c : ℂ) (f : ∀ n, Matrix (X n) (X n) ℂ) (k : ℕ) :
    spreadCoord X (c • f) k = c • spreadCoord X f k := by
  by_cases hex : ∃ n, Fintype.card (X n) = k + 1
  · rw [spreadCoord_of_hit X (c • f) hex, spreadCoord_of_hit X f hex,
      Pi.smul_apply, map_smul]
  · rw [spreadCoord_of_miss X _ hex, spreadCoord_of_miss X f hex, smul_zero]

theorem spreadCoord_star (f : ∀ n, Matrix (X n) (X n) ℂ) (k : ℕ) :
    spreadCoord X (star f) k = star (spreadCoord X f k) := by
  by_cases hex : ∃ n, Fintype.card (X n) = k + 1
  · rw [spreadCoord_of_hit X (star f) hex, spreadCoord_of_hit X f hex,
      Pi.star_apply, map_star]
  · rw [spreadCoord_of_miss X _ hex, spreadCoord_of_miss X f hex, star_zero]

theorem spreadCoord_mul (f g : ∀ n, Matrix (X n) (X n) ℂ) (k : ℕ) :
    spreadCoord X (f * g) k = spreadCoord X f k * spreadCoord X g k := by
  by_cases hex : ∃ n, Fintype.card (X n) = k + 1
  · rw [spreadCoord_of_hit X (f * g) hex, spreadCoord_of_hit X f hex,
      spreadCoord_of_hit X g hex, Pi.mul_apply, map_mul]
  · rw [spreadCoord_of_miss X _ hex, spreadCoord_of_miss X f hex,
      spreadCoord_of_miss X g hex, mul_zero]

/-! ## The spread map on bounded sequences -/

variable [∀ n, Nonempty (X n)]

/-- The spread of a bounded matrix sequence over `X` to a bounded matrix
sequence over the universal dimension sequence `k ↦ naturalFiniteModel
(k + 1)`. -/
def spreadSeq (a : BoundedMatrixSequence (fun n ↦ X n)) :
    BoundedMatrixSequence (fun k ↦ naturalFiniteModel (k + 1)) :=
  ⟨fun k ↦ spreadCoord X (fun n ↦ (a n : Matrix (X n) (X n) ℂ)) k,
    memℓp_infty ⟨‖a‖, by
      rintro _ ⟨k, rfl⟩
      exact norm_spreadCoord_le X _ ‖a‖
        (fun n ↦ boundedMatrixSequence_coord_norm_le (fun n ↦ X n) a n)
        (norm_nonneg a) k⟩⟩

omit [∀ n, Nonempty (X n)] in
@[simp] theorem spreadSeq_apply (a : BoundedMatrixSequence (fun n ↦ X n))
    (k : ℕ) :
    (spreadSeq X a k : Matrix (naturalFiniteModel (k + 1))
        (naturalFiniteModel (k + 1)) ℂ) =
      spreadCoord X (fun n ↦ (a n : Matrix (X n) (X n) ℂ)) k :=
  rfl

omit [∀ n, Nonempty (X n)] in
theorem spreadSeq_zero :
    spreadSeq X (0 : BoundedMatrixSequence (fun n ↦ X n)) = 0 := by
  refine lp.ext (funext fun k ↦ ?_)
  simp only [spreadSeq_apply, lp.coeFn_zero, Pi.zero_apply]
  exact spreadCoord_zero X k

omit [∀ n, Nonempty (X n)] in
theorem spreadSeq_add (a b : BoundedMatrixSequence (fun n ↦ X n)) :
    spreadSeq X (a + b) = spreadSeq X a + spreadSeq X b := by
  refine lp.ext (funext fun k ↦ ?_)
  simp only [spreadSeq_apply, lp.coeFn_add, Pi.add_apply]
  exact spreadCoord_add X _ _ k

omit [∀ n, Nonempty (X n)] in
theorem spreadSeq_sub (a b : BoundedMatrixSequence (fun n ↦ X n)) :
    spreadSeq X (a - b) = spreadSeq X a - spreadSeq X b := by
  refine lp.ext (funext fun k ↦ ?_)
  simp only [spreadSeq_apply, lp.coeFn_sub, Pi.sub_apply]
  exact spreadCoord_sub X _ _ k

theorem spreadSeq_smul (c : ℂ) (a : BoundedMatrixSequence (fun n ↦ X n)) :
    spreadSeq X (c • a) = c • spreadSeq X a := by
  refine lp.ext (funext fun k ↦ ?_)
  simp only [spreadSeq_apply, lp.coeFn_smul, Pi.smul_apply]
  exact spreadCoord_smul X c _ k

omit [∀ n, Nonempty (X n)] in
theorem spreadSeq_star (a : BoundedMatrixSequence (fun n ↦ X n)) :
    spreadSeq X (star a) = star (spreadSeq X a) := by
  refine lp.ext (funext fun k ↦ ?_)
  simp only [spreadSeq_apply, lp.coeFn_star, Pi.star_apply]
  exact spreadCoord_star X _ k

omit [∀ n, Nonempty (X n)] in
theorem spreadSeq_mul (a b : BoundedMatrixSequence (fun n ↦ X n)) :
    spreadSeq X (a * b) = spreadSeq X a * spreadSeq X b := by
  refine lp.ext (funext fun k ↦ ?_)
  simp only [spreadSeq_apply, lp.infty_coeFn_mul, Pi.mul_apply]
  exact spreadCoord_mul X _ _ k

/-! ## The spread map is exactly cofinite-null-reflecting -/

/-- **The isometry content of the printed remark.** A bounded matrix
sequence over a strictly increasing dimension sequence `X` is cofinite-null
exactly when its spread to the universal dimension sequence is
cofinite-null. This is what makes the induced corona map both well defined
and injective. -/
theorem isNull_spreadSeq_iff
    (hmono : StrictMono (fun n ↦ Fintype.card (X n)))
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    IsNullMatrixSequence (fun k ↦ naturalFiniteModel (k + 1)) cofinite
        (spreadSeq X a) ↔
      IsNullMatrixSequence (fun n ↦ X n) cofinite a := by
  have hcardpos : ∀ n, 0 < Fintype.card (X n) := fun n ↦ Fintype.card_pos
  have hcard_ge : ∀ n, n ≤ Fintype.card (X n) := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hmono (Nat.lt_succ_self n)))
  show Tendsto (fun k ↦ ‖(spreadSeq X a k : Matrix (naturalFiniteModel (k + 1))
        (naturalFiniteModel (k + 1)) ℂ)‖) cofinite (nhds 0) ↔
      Tendsto (fun n ↦ ‖(a n : Matrix (X n) (X n) ℂ)‖) cofinite (nhds 0)
  rw [Nat.cofinite_eq_atTop]
  constructor
  · intro hg
    have hcomp : Tendsto (fun n ↦ Fintype.card (X n) - 1) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      exact ⟨b + 1, fun n hn ↦ by have := hcard_ge n; omega⟩
    have hcompose : Tendsto (fun n ↦ ‖(spreadSeq X a (Fintype.card (X n) - 1) :
          Matrix (naturalFiniteModel (Fintype.card (X n) - 1 + 1))
            (naturalFiniteModel (Fintype.card (X n) - 1 + 1)) ℂ)‖)
        atTop (nhds 0) :=
      hg.comp hcomp
    have heq : (fun n ↦ ‖(spreadSeq X a (Fintype.card (X n) - 1) :
          Matrix (naturalFiniteModel (Fintype.card (X n) - 1 + 1))
            (naturalFiniteModel (Fintype.card (X n) - 1 + 1)) ℂ)‖) =
        (fun n ↦ ‖(a n : Matrix (X n) (X n) ℂ)‖) := by
      funext n
      have hcard1 : Fintype.card (X n) = (Fintype.card (X n) - 1) + 1 := by
        have := hcardpos n; omega
      rw [spreadSeq_apply]
      exact norm_spreadCoord_of_card_eq X hmono _ hcard1
    rw [heq] at hcompose
    exact hcompose
  · intro hf
    rw [Metric.tendsto_atTop] at hf ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hf ε hε
    refine ⟨Fintype.card (X N) - 1, fun k hk ↦ ?_⟩
    by_cases hex : ∃ n, Fintype.card (X n) = k + 1
    · obtain ⟨n, hn⟩ := hex
      have hnN : N ≤ n := by
        have h2 : Fintype.card (X N) ≤ k + 1 := by
          have := hcardpos N; omega
        rw [← hn] at h2
        exact hmono.le_iff_le.mp h2
      have hgk : ‖(spreadSeq X a k : Matrix (naturalFiniteModel (k + 1))
          (naturalFiniteModel (k + 1)) ℂ)‖ = ‖(a n : Matrix (X n) (X n) ℂ)‖ := by
        rw [spreadSeq_apply]
        exact norm_spreadCoord_of_card_eq X hmono _ hn
      rw [hgk]
      exact hN n hnN
    · have hzero : (spreadSeq X a k : Matrix (naturalFiniteModel (k + 1))
          (naturalFiniteModel (k + 1)) ℂ) = 0 := by
        rw [spreadSeq_apply]
        exact spreadCoord_of_not_hit X _ hex
      rw [hzero, norm_zero, dist_zero_right, norm_zero]
      exact hε

/-! ## The induced map on norm matrix coronas -/

/-- A chosen bounded representative of a corona class. -/
def spreadCoronaLift (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    BoundedMatrixSequence (fun n ↦ X n) :=
  Function.surjInv (normMatrixCStarCoronaMk_surjective (fun n ↦ X n)) x

theorem spreadCoronaLift_spec (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    normMatrixCStarCoronaMk (fun n ↦ X n) (spreadCoronaLift X x) = x :=
  Function.surjInv_eq _ x

/-- The spread map on coronas, computed on a chosen lift. -/
def spreadCorona (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    NormMatrixCStarCorona (fun k ↦ naturalFiniteModel (k + 1)) :=
  normMatrixCStarCoronaMk (fun k ↦ naturalFiniteModel (k + 1))
    (spreadSeq X (spreadCoronaLift X x))

/-- **Well-definedness.** Two lifts of the same class differ by a null
sequence, and `spreadSeq` carries null sequences to null sequences, so the
choice of lift does not matter. -/
theorem spreadCorona_mk (hmono : StrictMono (fun n ↦ Fintype.card (X n)))
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    spreadCorona X (normMatrixCStarCoronaMk (fun n ↦ X n) a) =
      normMatrixCStarCoronaMk (fun k ↦ naturalFiniteModel (k + 1))
        (spreadSeq X a) := by
  have hb : normMatrixCStarCoronaMk (fun n ↦ X n)
      (spreadCoronaLift X (normMatrixCStarCoronaMk (fun n ↦ X n) a))
      = normMatrixCStarCoronaMk (fun n ↦ X n) a :=
    spreadCoronaLift_spec X _
  have hnull : IsNullMatrixSequence (fun n ↦ X n) cofinite
      (spreadCoronaLift X (normMatrixCStarCoronaMk (fun n ↦ X n) a) - a) := by
    rw [← normMatrixCStarCoronaMk_eq_zero_iff, map_sub, hb, sub_self]
  have hnull' : IsNullMatrixSequence (fun k ↦ naturalFiniteModel (k + 1))
      cofinite
      (spreadSeq X (spreadCoronaLift X
          (normMatrixCStarCoronaMk (fun n ↦ X n) a)) - spreadSeq X a) := by
    rw [← spreadSeq_sub]
    exact (isNull_spreadSeq_iff X hmono _).mpr hnull
  have hzero : normMatrixCStarCoronaMk (fun k ↦ naturalFiniteModel (k + 1))
      (spreadSeq X (spreadCoronaLift X
          (normMatrixCStarCoronaMk (fun n ↦ X n) a)) - spreadSeq X a) = 0 :=
    (normMatrixCStarCoronaMk_eq_zero_iff _ _).mpr hnull'
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- **The spread map on coronas, as a nonunital `⋆`-homomorphism.** This is
the printed "resulting map on reduced products", proved to be a
`*`-homomorphism (it is isometric on the underlying matrix coordinates by
`norm_spreadCoord_of_card_eq`, and injective by `spreadCoronaHom_injective`
below). -/
def spreadCoronaHom (hmono : StrictMono (fun n ↦ Fintype.card (X n))) :
    NormMatrixCStarCorona (fun n ↦ X n) →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun k ↦ naturalFiniteModel (k + 1)) where
  toFun := spreadCorona X
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
    show spreadCorona X (c • normMatrixCStarCoronaMk (fun n ↦ X n) a)
      = c • spreadCorona X (normMatrixCStarCoronaMk (fun n ↦ X n) a)
    have hsmul : c • normMatrixCStarCoronaMk (fun n ↦ X n) a
        = normMatrixCStarCoronaMk (fun n ↦ X n) (c • a) :=
      (normMatrixCStarCoronaMk_smul (fun n ↦ X n) c a).symm
    rw [hsmul, spreadCorona_mk X hmono, spreadCorona_mk X hmono, spreadSeq_smul,
      normMatrixCStarCoronaMk_smul]
  map_zero' := by
    have h0 : spreadCorona X (normMatrixCStarCoronaMk (fun n ↦ X n) 0) = 0 := by
      rw [spreadCorona_mk X hmono, spreadSeq_zero, map_zero]
    rwa [map_zero] at h0
  map_add' x y := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
    obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) y
    have hsum : normMatrixCStarCoronaMk (fun n ↦ X n) a
          + normMatrixCStarCoronaMk (fun n ↦ X n) b
        = normMatrixCStarCoronaMk (fun n ↦ X n) (a + b) :=
      (map_add (normMatrixCStarCoronaMk (fun n ↦ X n)) a b).symm
    rw [hsum, spreadCorona_mk X hmono, spreadCorona_mk X hmono,
      spreadCorona_mk X hmono, spreadSeq_add, map_add]
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
    obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) y
    have hprod : normMatrixCStarCoronaMk (fun n ↦ X n) a
          * normMatrixCStarCoronaMk (fun n ↦ X n) b
        = normMatrixCStarCoronaMk (fun n ↦ X n) (a * b) :=
      (map_mul (normMatrixCStarCoronaMk (fun n ↦ X n)) a b).symm
    rw [hprod, spreadCorona_mk X hmono, spreadCorona_mk X hmono,
      spreadCorona_mk X hmono, spreadSeq_mul, map_mul]
  map_star' x := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
    rw [normMatrixCStarCorona_star_mk, spreadCorona_mk X hmono,
      spreadCorona_mk X hmono, spreadSeq_star, normMatrixCStarCorona_star_mk]

@[simp] theorem spreadCoronaHom_apply
    (hmono : StrictMono (fun n ↦ Fintype.card (X n)))
    (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    spreadCoronaHom X hmono x = spreadCorona X x := rfl

/-- **The spread map on coronas is injective.** Directly from
`isNull_spreadSeq_iff`: a difference of lifts is null exactly when its
spread image is. -/
theorem spreadCoronaHom_injective
    (hmono : StrictMono (fun n ↦ Fintype.card (X n))) :
    Function.Injective (spreadCoronaHom X hmono) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
  obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) y
  rw [spreadCoronaHom_apply, spreadCoronaHom_apply, spreadCorona_mk X hmono,
    spreadCorona_mk X hmono, ← sub_eq_zero, ← map_sub,
    normMatrixCStarCoronaMk_eq_zero_iff, ← spreadSeq_sub] at hxy
  rw [← sub_eq_zero, ← map_sub, normMatrixCStarCoronaMk_eq_zero_iff]
  exact (isNull_spreadSeq_iff X hmono (a - b)).mp hxy

end

/-! ## The closed statement -/

noncomputable section

/-- **Sentence `49af36bf9b2e`, closed.** "The resulting map on reduced
products is an isometric `*`-homomorphism, so the MF algebras of Section
`sec:prelim` are exactly the separable `C^*`-algebras that embed in
`∏_kM_k(ℂ)/⊕_kM_k(ℂ)`." Both directions: the forward direction composes an
`IsMFAlgebra` embedding (which, by definition, already lands in a corona
over a strictly increasing dimension sequence) with `spreadCoronaHom`; the
converse is immediate, since the universal corona is itself a norm matrix
corona over the (strictly increasing) sequence `k ↦ k + 1`. -/
theorem isMFAlgebra_iff_embeds_universalCorona
    (A : Type u) [NonUnitalCStarAlgebra A] :
    IsMFAlgebra A ↔
      TopologicalSpace.SeparableSpace A ∧
        ∃ e : A →⋆ₙₐ[ℂ]
            NormMatrixCStarCorona (fun k ↦ naturalFiniteModel (k + 1)),
          Function.Injective e := by
  constructor
  · rintro ⟨hsep, X, hne, _hpos, hmono, e, he⟩
    letI : ∀ n, Nonempty (X n) := hne
    exact ⟨hsep, (spreadCoronaHom X hmono).comp e,
      (spreadCoronaHom_injective X hmono).comp he⟩
  · rintro ⟨hsep, e, he⟩
    refine ⟨hsep, (fun k ↦ naturalFiniteModel (k + 1)), ?_, ?_, ?_, e, he⟩
    · exact fun k ↦ ⟨⟨0, Nat.succ_pos k⟩⟩
    · exact fun k ↦ by simp only [Fintype.card_fin]; omega
    · apply strictMono_nat_of_lt_succ
      intro k
      simp only [Fintype.card_fin]
      omega

end

end CoronaEmbeddingRemark
end MFRecognition
end Manuscript
end GroupApproximation
