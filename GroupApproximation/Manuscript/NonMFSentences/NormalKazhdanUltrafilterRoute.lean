import GroupApproximation.Manuscript.NonMFSentences.CompressionSentencesB2
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaEmbedding
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:normal-kazhdan` along the printed ultrafilter route

`non_mf_groups_exist.tex`, proof of Theorem `thm:normal-kazhdan` (tex lines
655-701 at 73c867c5b).  After the corner step, the printed proof reads:

> Let `π : C*_max(K) → 𝒬_r` be the homomorphism induced by `Θ̂|_K`.  Since `q`
> commutes with `Θ(K)`, the map `a ↦ qΘ(a)` is a homomorphism on `C*_max(K)`
> agreeing with `π` on `K`, so `π(e_K)` is the coordinate restriction of
> `qp = 0`.
>
> Fix a free ultrafilter `ω` and let `τ` be the limit along `ω` of the
> normalized traces of the coordinates `M_{r_n}(ℂ)`.  A norm-null sequence has
> vanishing traces, since `|tr_{r_n}(x)| ≤ ‖x‖`, so `τ` is a well defined
> tracial state on `𝒬_r`.  The hypothesis applies to `(W_n)` itself, so
> `|tr_{r_n}(W_n(k)) − 1| ≤ ‖W_n(k) − I_{r_n}‖₂ → 0` for `k ∈ K` in the
> normalized Hilbert--Schmidt norm of `M_{r_n}(ℂ)`, and therefore
> `τ(π(u_k)) = 1` for every `k ∈ K`, where `u_k` is the canonical unitary of
> `k`.  The trivial character `χ` of `K` is the state of `C*_max(K)` with
> `χ(u_k) = 1` for every `k`, and it has `χ(e_K) = 1`.  The two states `τ∘π`
> and `χ` agree on every `u_k`, hence by linearity on the dense subalgebra
> `ℂ[K]`, hence on `C*_max(K)`.  So `1 = χ(e_K) = τ(π(e_K)) = τ(0) = 0`, a
> contradiction.

`Manuscript/OneSidedMFRadical/NormalKazhdanPrintedRoute.lean` proves the theorem
by an ultrafilter-free `limsup` estimate, which is a different argument.  This
module carries the printed sentences on their own terms and assembles the
theorem from them:

* `cornerCoronaUnitaryHom D` is the corona homomorphism `Θ̂` of the corner
  representation `(W_n)` into the unitary group of `𝒬_r`;
* `cornerCoronaEmbedCLM` is the printed identification of `𝒬_r` with the corner
  `q 𝒬_d q` (on the retained coordinates), an isometry, so `π(e_K) = 0` holds
  in `𝒬_r` itself once its image is the coordinate restriction of `q p = 0`;
* `τ` is the continuous linear functional of `CompressionSentencesB2.lean`, and
  it is a tracial state at the level of the corona;
* the agreement of `τ∘π` and `χ` passes from the generators to `ℂ[K]` by
  linearity and to `C*_max(K)` by density and continuity
  (`maximalGroupCStar_ext_of_generator`);
* `1 = χ(e_K) = τ(π(e_K)) = τ(0) = 0`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Filter Matrix Topology
open MaximalCStarKazhdanProjection
open OneSidedMFRadical
open OneSidedMFRadical.NormalKazhdanPrintedRoute
open PrintedCornerCompression
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## `τ` is a tracial state on `𝒬_r` -/

theorem ultrafilterNormalizedTraceCLM_mk (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    ultrafilterNormalizedTraceCLM X ω hω (normMatrixCStarCoronaMk (fun n ↦ X n) a)
      = TracialUltraproduct.seqUltratrace X ω a := by
  rw [ultrafilterNormalizedTraceCLM_apply, ultrafilterNormalizedTraceAdd_mk]

/-- **`thm:normal-kazhdan`, proof sentence (tex lines 680-684), at the corona.**

> Fix a free ultrafilter `ω` and let `τ` be the limit along `ω` of the
> normalized traces of the coordinates `M_{r_n}(ℂ)`.  A norm-null sequence has
> vanishing traces, since `|tr_{r_n}(x)| ≤ ‖x‖`, so `τ` is a well defined
> tracial state on `𝒬_r`.

`τ` is a continuous linear functional on the corona `𝒬_r` itself
(`ultrafilterNormalizedTraceCLM`), its value at the class of `(x_n)` is the
limit along `ω` of the normalized traces, it is bounded by the norm, it is
unital, positive and tracial. -/
def UltrafilterTraceIsTracialStateOnCorona : Prop :=
  ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite),
    (∀ a : BoundedMatrixSequence (fun n ↦ X n),
        ultrafilterNormalizedTraceCLM X ω hω (normMatrixCStarCoronaMk (fun n ↦ X n) a)
          = UltrafilterLimit.ulim ω (fun n ↦ normTrace (X n) (a n))) ∧
      (∀ x : NormMatrixCStarCorona (fun n ↦ X n),
        ‖ultrafilterNormalizedTraceCLM X ω hω x‖ ≤ ‖x‖) ∧
      ultrafilterNormalizedTraceCLM X ω hω 1 = 1 ∧
      (∀ x : NormMatrixCStarCorona (fun n ↦ X n), ∃ t : ℝ, 0 ≤ t ∧
        ultrafilterNormalizedTraceCLM X ω hω (star x * x) = (t : ℂ)) ∧
      (∀ x y : NormMatrixCStarCorona (fun n ↦ X n),
        ultrafilterNormalizedTraceCLM X ω hω (x * y)
          = ultrafilterNormalizedTraceCLM X ω hω (y * x))

theorem manuscriptSentence_ultrafilterTraceIsTracialStateOnCorona :
    UltrafilterTraceIsTracialStateOnCorona := by
  intro X _ ω hω
  refine ⟨fun a ↦ ?_, fun x ↦ ?_, ?_, fun x ↦ ?_, fun x y ↦ ?_⟩
  · rw [ultrafilterNormalizedTraceCLM_mk]
    rfl
  · rw [ultrafilterNormalizedTraceCLM_apply]
    exact norm_ultrafilterNormalizedTraceAdd_le X ω hω x
  · rw [← RingHom.map_one (normMatrixCStarCoronaMk (fun n ↦ X n)),
      ultrafilterNormalizedTraceCLM_mk]
    exact TracialUltraproduct.seqUltratrace_one X ω
  · obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
    rw [normMatrixCStarCorona_star_mk,
      ← RingHom.map_mul (normMatrixCStarCoronaMk (fun n ↦ X n)), ultrafilterNormalizedTraceCLM_mk]
    exact ⟨TracialUltraproduct.seqHSLimit X ω a,
      TracialUltraproduct.seqHSLimit_nonneg X ω a,
      TracialUltraproduct.seqUltratrace_star_mul_self X ω a⟩
  · obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
    obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) y
    rw [← RingHom.map_mul (normMatrixCStarCoronaMk (fun n ↦ X n)) a b,
      ← RingHom.map_mul (normMatrixCStarCoronaMk (fun n ↦ X n)) b a,
      ultrafilterNormalizedTraceCLM_mk,
      ultrafilterNormalizedTraceCLM_mk]
    exact TracialUltraproduct.seqUltratrace_mul_comm X ω a b

/-! ## `Θ̂`: the corona homomorphism of the corner representation -/

/-- The corner models are nonempty. -/
instance printedCornerModelNonempty {G : Type*} [Group G] {model : ℕ → FiniteModel}
    (D : PrintedCornerData G model) (n : ℕ) : Nonempty (D.cornerModel n) :=
  Fintype.card_pos_iff.mp (D.cornerModel_card_pos n)

/-- **The printed `Θ̂`.**  The corner representation `(W_n) = (D.cornerMap n)` is
an operator norm asymptotic representation, so its classes form a homomorphism
into the unitary group of the corona `𝒬_r` over the corner models. -/
def cornerCoronaUnitaryHom {G : Type*} [Group G] {model : ℕ → FiniteModel}
    (D : PrintedCornerData G model) :
    G →* unitary (NormMatrixCStarCorona (fun n ↦ D.cornerModel n)) :=
  MonoidHom.mk'
    (fun g ↦ unitarySequenceToCorona (fun n ↦ D.cornerModel n)
      (fun n ↦ D.cornerMap n g))
    (fun g h ↦ by
      apply Subtype.ext
      change normMatrixCStarCoronaMk (fun n ↦ D.cornerModel n)
          (unitarySequenceBounded (fun n ↦ D.cornerModel n)
            (fun n ↦ D.cornerMap n (g * h)))
        = normMatrixCStarCoronaMk (fun n ↦ D.cornerModel n)
            (unitarySequenceBounded (fun n ↦ D.cornerModel n)
              (fun n ↦ D.cornerMap n g))
          * normMatrixCStarCoronaMk (fun n ↦ D.cornerModel n)
            (unitarySequenceBounded (fun n ↦ D.cornerModel n)
              (fun n ↦ D.cornerMap n h))
      rw [← RingHom.map_mul (normMatrixCStarCoronaMk (fun n ↦ D.cornerModel n)), ← sub_eq_zero,
        ← RingHom.map_sub (normMatrixCStarCoronaMk (fun n ↦ D.cornerModel n)),
        normMatrixCStarCoronaMk_eq_zero_iff, IsNullMatrixSequence, Nat.cofinite_eq_atTop]
      refine (D.cornerMap_mul_defect_tendsto g h).congr fun n ↦ ?_
      rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_mul, Pi.mul_apply]
      rfl)

/-! ## The identification of `𝒬_r` with the corner, as an isometry -/

theorem cornerEmbedSeq_zero (Y : ℕ → FiniteModel) (P : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hP : ∀ n, (P n).IsHermitian) :
    CornerCoronaEmbedding.cornerEmbedSeq Y P hP 0 = 0 := by
  refine lp.ext (funext fun n ↦ ?_)
  rw [CornerCoronaEmbedding.cornerEmbedSeq_apply]
  exact NormalKazhdanPrintedRoute.cornerEmbed_zero (hP n)

theorem cornerEmbedSeq_add (Y : ℕ → FiniteModel) (P : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hP : ∀ n, (P n).IsHermitian)
    (c d : BoundedMatrixSequence (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n)) :
    CornerCoronaEmbedding.cornerEmbedSeq Y P hP (c + d)
      = CornerCoronaEmbedding.cornerEmbedSeq Y P hP c
        + CornerCoronaEmbedding.cornerEmbedSeq Y P hP d := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [CornerCoronaEmbedding.cornerEmbedSeq_apply, lp.coeFn_add, Pi.add_apply]
  exact NormalKazhdanPrintedRoute.cornerEmbed_add (hP n) (c n) (d n)

set_option synthInstance.maxHeartbeats 80000 in
theorem cornerEmbedSeq_smul (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (P : ∀ n, Matrix (Y n) (Y n) ℂ) (hP : ∀ n, (P n).IsHermitian)
    [∀ n, Nonempty (CornerCoronaEmbedding.cornerModel Y P hP n)] (z : ℂ)
    (c : BoundedMatrixSequence (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n)) :
    CornerCoronaEmbedding.cornerEmbedSeq Y P hP
        (z • c : BoundedMatrixSequence (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n))
      = (z • CornerCoronaEmbedding.cornerEmbedSeq Y P hP c :
          BoundedMatrixSequence (fun n ↦ Y n)) := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [CornerCoronaEmbedding.cornerEmbedSeq_apply, lp.coeFn_smul, Pi.smul_apply]
  exact NormalKazhdanPrintedRoute.cornerEmbed_smul (hP n) z (c n)

/-- The printed passage `(c_n) ↦ (J_n c_n J_n*)`, read in the ambient corona. -/
def cornerEmbedSeqAddHom (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (P : ∀ n, Matrix (Y n) (Y n) ℂ) (hP : ∀ n, (P n).IsHermitian) :
    BoundedMatrixSequence (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) →+
      NormMatrixCStarCorona (fun n ↦ Y n) where
  toFun c := normMatrixCStarCoronaMk (fun n ↦ Y n)
    (CornerCoronaEmbedding.cornerEmbedSeq Y P hP c)
  map_zero' := by
    rw [cornerEmbedSeq_zero, RingHom.map_zero (normMatrixCStarCoronaMk (fun n ↦ Y n))]
  map_add' c d := by
    rw [cornerEmbedSeq_add, RingHom.map_add (normMatrixCStarCoronaMk (fun n ↦ Y n))]

theorem nullIdeal_le_cornerEmbedSeqAddHom_ker (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (P : ∀ n, Matrix (Y n) (Y n) ℂ) (hP : ∀ n, (P n).IsHermitian)
    [∀ n, Nonempty (CornerCoronaEmbedding.cornerModel Y P hP n)] :
    (nullMatrixSequenceIdeal (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n)
        cofinite).toAddSubgroup ≤ (cornerEmbedSeqAddHom Y P hP).ker := by
  intro c hc
  change normMatrixCStarCoronaMk (fun n ↦ Y n)
    (CornerCoronaEmbedding.cornerEmbedSeq Y P hP c) = 0
  have hnull : IsNullMatrixSequence
      (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) cofinite c := hc
  have hmk0 : normMatrixCStarCoronaMk
        (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) c
      = normMatrixCStarCoronaMk
        (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) 0 := by
    rw [RingHom.map_zero (normMatrixCStarCoronaMk
      (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n))]
    exact (normMatrixCStarCoronaMk_eq_zero_iff
      (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) c).mpr hnull
  rw [CornerCoronaEmbedding.mk_cornerEmbedSeq_congr Y P hP c 0 hmk0,
    cornerEmbedSeq_zero, RingHom.map_zero (normMatrixCStarCoronaMk (fun n ↦ Y n))]

/-- **The printed identification of `𝒬_r` with the corner, on classes.** -/
def cornerCoronaEmbedAdd (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (P : ∀ n, Matrix (Y n) (Y n) ℂ) (hP : ∀ n, (P n).IsHermitian)
    [∀ n, Nonempty (CornerCoronaEmbedding.cornerModel Y P hP n)] :
    NormMatrixCStarCorona (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) →+
      NormMatrixCStarCorona (fun n ↦ Y n) := by
  unfold NormMatrixCStarCorona
  exact QuotientAddGroup.lift
    (nullMatrixSequenceIdeal (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n)
      cofinite).toAddSubgroup
    (cornerEmbedSeqAddHom Y P hP) (nullIdeal_le_cornerEmbedSeqAddHom_ker Y P hP)

@[simp] theorem cornerCoronaEmbedAdd_mk (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (P : ∀ n, Matrix (Y n) (Y n) ℂ) (hP : ∀ n, (P n).IsHermitian)
    [∀ n, Nonempty (CornerCoronaEmbedding.cornerModel Y P hP n)]
    (c : BoundedMatrixSequence (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n)) :
    cornerCoronaEmbedAdd Y P hP
        (normMatrixCStarCoronaMk (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) c)
      = normMatrixCStarCoronaMk (fun n ↦ Y n)
          (CornerCoronaEmbedding.cornerEmbedSeq Y P hP c) := by
  unfold cornerCoronaEmbedAdd normMatrixCStarCoronaMk NormMatrixCStarCorona
  exact QuotientAddGroup.lift_mk _ _ _

theorem cornerCoronaEmbedAdd_smul (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (P : ∀ n, Matrix (Y n) (Y n) ℂ) (hP : ∀ n, (P n).IsHermitian)
    [∀ n, Nonempty (CornerCoronaEmbedding.cornerModel Y P hP n)] (z : ℂ)
    (x : NormMatrixCStarCorona (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n)) :
    cornerCoronaEmbedAdd Y P hP (z • x) = z • cornerCoronaEmbedAdd Y P hP x := by
  obtain ⟨c, rfl⟩ := normMatrixCStarCoronaMk_surjective
    (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) x
  have hsC : z • normMatrixCStarCoronaMk
        (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) c
      = normMatrixCStarCoronaMk
        (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) (z • c) := by
    show z • normMatrixCStarCoronaQuotient
        (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) c
      = normMatrixCStarCoronaQuotient
        (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) (z • c)
    exact (map_smul (normMatrixCStarCoronaQuotient
      (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n)) z c).symm
  have hsY : z • normMatrixCStarCoronaMk (fun n ↦ Y n)
        (CornerCoronaEmbedding.cornerEmbedSeq Y P hP c)
      = normMatrixCStarCoronaMk (fun n ↦ Y n)
        (z • CornerCoronaEmbedding.cornerEmbedSeq Y P hP c) := by
    show z • normMatrixCStarCoronaQuotient (fun n ↦ Y n)
        (CornerCoronaEmbedding.cornerEmbedSeq Y P hP c)
      = normMatrixCStarCoronaQuotient (fun n ↦ Y n)
        (z • CornerCoronaEmbedding.cornerEmbedSeq Y P hP c)
    exact (map_smul (normMatrixCStarCoronaQuotient (fun n ↦ Y n)) z
      (CornerCoronaEmbedding.cornerEmbedSeq Y P hP c)).symm
  rw [hsC, cornerCoronaEmbedAdd_mk, cornerCoronaEmbedAdd_mk, cornerEmbedSeq_smul, hsY]

theorem norm_cornerCoronaEmbedAdd (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (P : ∀ n, Matrix (Y n) (Y n) ℂ) (hP : ∀ n, (P n).IsHermitian)
    [∀ n, Nonempty (CornerCoronaEmbedding.cornerModel Y P hP n)]
    (x : NormMatrixCStarCorona (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n)) :
    ‖cornerCoronaEmbedAdd Y P hP x‖ = ‖x‖ := by
  obtain ⟨c, rfl⟩ := normMatrixCStarCoronaMk_surjective
    (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) x
  rw [cornerCoronaEmbedAdd_mk]
  exact CornerCoronaEmbedding.norm_mk_cornerEmbedSeq Y P hP c

/-- **The printed identification of `𝒬_r` with the corner `q 𝒬_d q`**, as a
continuous linear isometry into the ambient corona. -/
def cornerCoronaEmbedCLM (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (P : ∀ n, Matrix (Y n) (Y n) ℂ) (hP : ∀ n, (P n).IsHermitian)
    [∀ n, Nonempty (CornerCoronaEmbedding.cornerModel Y P hP n)] :
    NormMatrixCStarCorona (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n) →L[ℂ]
      NormMatrixCStarCorona (fun n ↦ Y n) :=
  LinearMap.mkContinuous
    { toFun := cornerCoronaEmbedAdd Y P hP
      map_add' := map_add (cornerCoronaEmbedAdd Y P hP)
      map_smul' := fun z x ↦ cornerCoronaEmbedAdd_smul Y P hP z x }
    1 (fun x ↦ by
      rw [one_mul]
      exact (norm_cornerCoronaEmbedAdd Y P hP x).le)

theorem cornerCoronaEmbedCLM_apply (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (P : ∀ n, Matrix (Y n) (Y n) ℂ) (hP : ∀ n, (P n).IsHermitian)
    [∀ n, Nonempty (CornerCoronaEmbedding.cornerModel Y P hP n)]
    (x : NormMatrixCStarCorona (fun n ↦ CornerCoronaEmbedding.cornerModel Y P hP n)) :
    cornerCoronaEmbedCLM Y P hP x = cornerCoronaEmbedAdd Y P hP x := rfl

/-! ## `π(e_K) = 0` in `𝒬_r` -/

/-- The map `a ↦ (q Θ(a))` restricted to the retained coordinates, with
`q = 1 − p`, as a continuous linear map on `C*_max(L)`.  Continuity is the
bound `‖(q f(a))|‖ ≤ ‖q‖ ‖a‖`, from the contractivity of the two
`⋆`-homomorphisms. -/
def complementRestrictCLM {L : Type} [Group L] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (p : NormMatrixCStarCorona (fun n ↦ X n))
    (f : MaximalGroupCStar L →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)) :
    MaximalGroupCStar L →L[ℂ] NormMatrixCStarCorona (fun k ↦ X (φ k)) :=
  LinearMap.mkContinuous
    ((coronaRestrictAlg X φ hφ).toAlgHom.toLinearMap.comp
      ((LinearMap.mulLeft ℂ ((1 : NormMatrixCStarCorona (fun n ↦ X n)) - p)).comp
        f.toAlgHom.toLinearMap))
    ‖(1 : NormMatrixCStarCorona (fun n ↦ X n)) - p‖
    (fun x ↦ by
      show ‖coronaRestrictAlg X φ hφ
          (((1 : NormMatrixCStarCorona (fun n ↦ X n)) - p) * f x)‖
        ≤ ‖(1 : NormMatrixCStarCorona (fun n ↦ X n)) - p‖ * ‖x‖
      calc ‖coronaRestrictAlg X φ hφ
            (((1 : NormMatrixCStarCorona (fun n ↦ X n)) - p) * f x)‖
          ≤ ‖((1 : NormMatrixCStarCorona (fun n ↦ X n)) - p) * f x‖ :=
            NonUnitalStarAlgHom.norm_apply_le (coronaRestrictAlg X φ hφ) _
        _ ≤ ‖(1 : NormMatrixCStarCorona (fun n ↦ X n)) - p‖ * ‖f x‖ := norm_mul_le _ _
        _ ≤ ‖(1 : NormMatrixCStarCorona (fun n ↦ X n)) - p‖ * ‖x‖ :=
            mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le f x)
              (norm_nonneg _))

/-- A `⋆`-homomorphism out of a maximal group `C*`-algebra, as a continuous
linear map (a `⋆`-homomorphism of `C*`-algebras is contractive). -/
def starAlgHomCLM {L : Type} [Group L] {A : Type} [CStarAlgebra A]
    (π : MaximalGroupCStar L →⋆ₐ[ℂ] A) : MaximalGroupCStar L →L[ℂ] A :=
  LinearMap.mkContinuous π.toAlgHom.toLinearMap 1
    (fun x ↦ by
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le π x)

@[simp] theorem starAlgHomCLM_apply {L : Type} [Group L] {A : Type} [CStarAlgebra A]
    (π : MaximalGroupCStar L →⋆ₐ[ℂ] A) (x : MaximalGroupCStar L) :
    starAlgHomCLM π x = π x := rfl

/-- **`thm:normal-kazhdan`, proof sentence (tex lines 674-678).**

> Let `π : C*_max(K) → 𝒬_r` be the homomorphism induced by `Θ̂|_K`.  Since `q`
> commutes with `Θ(K)`, the map `a ↦ qΘ(a)` is a homomorphism on `C*_max(K)`
> agreeing with `π` on `K`, so `π(e_K)` is the coordinate restriction of
> `qp = 0`.

`π` is any homomorphism with `π(u_s) = Θ̂(s)`; `hclass` is the corner lemma's
identification of the class of `(J_n W_n(g) J_n*)` with the coordinate
restriction of `qΘ(g)`.  The identification of `𝒬_r` with the corner agrees with
`a ↦ (qΘ(a))|` on every generator, hence (continuity and density) everywhere; at
`e_K` the right side is the restriction of `qp = 0`, and the identification is
an isometry, so `π(e_K) = 0` in `𝒬_r`. -/
theorem manuscriptSentence_inducedCornerKazhdanProjectionZero
    {G : Type} [Group G] {L : Type} [Group L]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (KD : KazhdanData L)
    (f : MaximalGroupCStar L →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (iota : L →* G)
    (hf : ∀ s : L, f (maximalGroupCStarGenerator L s)
      = ((rho (iota s) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)))
    (hzero : ((1 : NormMatrixCStarCorona (fun n ↦ X n)) - f KD.projection)
      * f KD.projection = 0)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (D : PrintedCornerData G (fun k ↦ X (φ k)))
    (hclass : ∀ g : G,
      normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g)
        = coronaRestrict X φ hφ
            ((1 - f KD.projection) *
              ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n))))
    (π : MaximalGroupCStar L →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ D.cornerModel n))
    (hπ : ∀ s : L, π (maximalGroupCStarGenerator L s)
      = ((cornerCoronaUnitaryHom D (iota s) :
          unitary (NormMatrixCStarCorona (fun n ↦ D.cornerModel n))) :
            NormMatrixCStarCorona (fun n ↦ D.cornerModel n))) :
    π KD.projection = 0 := by
  classical
  haveI : ∀ n, Nonempty
      (CornerCoronaEmbedding.cornerModel (fun k ↦ X (φ k)) D.q D.qHermitian n) :=
    fun n ↦ Fintype.card_pos_iff.mp (D.cornerModel_card_pos n)
  have hext : (cornerCoronaEmbedCLM (fun k ↦ X (φ k)) D.q D.qHermitian).comp
      (starAlgHomCLM π) = complementRestrictCLM X φ hφ (f KD.projection) f := by
    refine maximalGroupCStar_ext_of_generator L fun s ↦ ?_
    change cornerCoronaEmbedCLM (fun k ↦ X (φ k)) D.q D.qHermitian
        (π (maximalGroupCStarGenerator L s))
      = coronaRestrictAlg X φ hφ
          ((1 - f KD.projection) * f (maximalGroupCStarGenerator L s))
    rw [hπ s, hf s, coronaRestrictAlg_apply, ← hclass (iota s)]
    change cornerCoronaEmbedAdd (fun k ↦ X (φ k)) D.q D.qHermitian
        (normMatrixCStarCoronaMk
          (fun n ↦ CornerCoronaEmbedding.cornerModel (fun k ↦ X (φ k)) D.q
            D.qHermitian n)
          (unitarySequenceBounded (fun n ↦ D.cornerModel n)
            (fun n ↦ D.cornerMap n (iota s)))) = _
    rw [cornerCoronaEmbedAdd_mk]
    exact congrArg (normMatrixCStarCoronaMk (fun k ↦ X (φ k)))
      (lp.ext (funext fun n ↦ rfl))
  have hΨ : cornerCoronaEmbedCLM (fun k ↦ X (φ k)) D.q D.qHermitian
      (π KD.projection) = 0 := by
    have h := congrArg
      (fun F : MaximalGroupCStar L →L[ℂ] NormMatrixCStarCorona (fun k ↦ X (φ k)) ↦
        F KD.projection) hext
    change cornerCoronaEmbedCLM (fun k ↦ X (φ k)) D.q D.qHermitian (π KD.projection)
      = coronaRestrictAlg X φ hφ ((1 - f KD.projection) * f KD.projection) at h
    rw [h, hzero, coronaRestrictAlg_apply, RingHom.map_zero (coronaRestrict X φ hφ)]
  have hnorm : ‖π KD.projection‖ = 0 := by
    rw [← norm_cornerCoronaEmbedAdd (fun k ↦ X (φ k)) D.q D.qHermitian
      (π KD.projection), ← cornerCoronaEmbedCLM_apply, hΨ, norm_zero]
  exact norm_eq_zero.mp hnorm

/-! ## `τ(π(u_k)) = 1` -/

/-- **`thm:normal-kazhdan`, proof sentence (tex lines 684-691).**

> The hypothesis applies to `(W_n)` itself, so
> `|tr_{r_n}(W_n(k)) − 1| ≤ ‖W_n(k) − I_{r_n}‖₂ → 0` `(k ∈ K)` in the
> normalized Hilbert--Schmidt norm of `M_{r_n}(ℂ)`, and therefore
> `τ(π(u_k)) = 1` for every `k ∈ K`, where `u_k` is the canonical unitary of `k`.

The trace estimate is
`NormalKazhdanPrintedRoute.manuscriptSentence_traceOfCombinationTendsTo`, and
`CompressionSentencesB.manuscriptSentence_ultrafilterTraceOfCornerUnitaryIsOne`
passes it to the free ultrafilter. -/
theorem manuscriptSentence_ultrafilterTraceOfInducedGeneratorIsOne
    {G : Type} [Group G] {L : Type} [Group L] (iota : L →* G)
    (hres : ∀ s : L, iota s ∈ opToHSShadowResidual G)
    {model : ℕ → FiniteModel} (D : PrintedCornerData G model)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (π : MaximalGroupCStar L →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ D.cornerModel n))
    (hπ : ∀ s : L, π (maximalGroupCStarGenerator L s)
      = ((cornerCoronaUnitaryHom D (iota s) :
          unitary (NormMatrixCStarCorona (fun n ↦ D.cornerModel n))) :
            NormMatrixCStarCorona (fun n ↦ D.cornerModel n)))
    (s : L) :
    ultrafilterNormalizedTraceCLM (fun n ↦ D.cornerModel n) ω hω
      (π (maximalGroupCStarGenerator L s)) = 1 := by
  rw [hπ s]
  change ultrafilterNormalizedTraceCLM (fun n ↦ D.cornerModel n) ω hω
      (normMatrixCStarCoronaMk (fun n ↦ D.cornerModel n)
        (unitarySequenceBounded (fun n ↦ D.cornerModel n)
          (fun n ↦ D.cornerMap n (iota s)))) = 1
  rw [ultrafilterNormalizedTraceCLM_mk]
  exact manuscriptSentence_ultrafilterTraceOfCornerUnitaryIsOne iota hres D ω hω s

/-! ## The trivial character -/

/-- **`thm:normal-kazhdan`, proof sentence (tex lines 692-694).**

> The trivial character `χ` of `K` is the state of `C*_max(K)` with
> `χ(u_k) = 1` for every `k`, and it has `χ(e_K) = 1`.

`χ = maximalGroupCStarTrivialCharacter K`: a unital, positive functional (a
state) with the two printed values. -/
theorem manuscriptSentence_trivialCharacterIsStateWithValues
    {K : Type} [Group K] (KD : KazhdanData K) :
    maximalGroupCStarTrivialCharacter K 1 = 1 ∧
      (∀ x : MaximalGroupCStar K, ∃ t : ℝ, 0 ≤ t ∧
        maximalGroupCStarTrivialCharacter K (star x * x) = (t : ℂ)) ∧
      (∀ k : K, maximalGroupCStarTrivialCharacter K
        (maximalGroupCStarGenerator K k) = 1) ∧
      maximalGroupCStarTrivialCharacter K KD.projection = 1 := by
  refine ⟨map_one _, fun x ↦
    ⟨‖maximalGroupCStarTrivialCharacter K x‖ ^ 2, by positivity, ?_⟩,
    maximalGroupCStarTrivialCharacter_generator K,
    maximalGroupCStarTrivialCharacter_kazhdanProjection KD⟩
  rw [map_mul (maximalGroupCStarTrivialCharacter K), map_star (maximalGroupCStarTrivialCharacter K),
    Complex.ofReal_pow]
  exact Complex.conj_mul' _

/-! ## The two states agree -/

/-- **`thm:normal-kazhdan`, proof sentence (tex lines 694-696).**

> The two states `τ∘π` and `χ` agree on every `u_k`, hence by linearity on the
> dense subalgebra `ℂ[K]`, hence on `C*_max(K)`.

The three clauses in the printed order: the generators, every finite linear
combination of generators, and the whole algebra (continuity and density of
`ℂ[K]`, `maximalGroupCStar_ext_of_generator`). -/
theorem manuscriptSentence_statesAgreeOnGeneratorsSpanAndAlgebra
    {L : Type} [Group L] {A : Type} [CStarAlgebra A]
    (π : MaximalGroupCStar L →⋆ₐ[ℂ] A) (τ : A →L[ℂ] ℂ)
    (hτπ : ∀ s : L, τ (π (maximalGroupCStarGenerator L s)) = 1) :
    (∀ s : L, τ (π (maximalGroupCStarGenerator L s))
        = maximalGroupCStarTrivialCharacter L (maximalGroupCStarGenerator L s)) ∧
      (∀ (F : Finset L) (α : L → ℂ),
        τ (π (∑ s ∈ F, α s • maximalGroupCStarGenerator L s))
          = maximalGroupCStarTrivialCharacter L
              (∑ s ∈ F, α s • maximalGroupCStarGenerator L s)) ∧
      ∀ x : MaximalGroupCStar L, τ (π x) = maximalGroupCStarTrivialCharacter L x := by
  have hgen : ∀ s : L, τ (π (maximalGroupCStarGenerator L s))
      = maximalGroupCStarTrivialCharacter L (maximalGroupCStarGenerator L s) := by
    intro s
    rw [hτπ s, maximalGroupCStarTrivialCharacter_generator]
  refine ⟨hgen, fun F α ↦ ?_, fun x ↦ ?_⟩
  · simp only [map_sum, map_smul, hgen]
  · have hext : τ.comp (starAlgHomCLM π)
        = starAlgHomCLM (maximalGroupCStarTrivialCharacter L) :=
      maximalGroupCStar_ext_of_generator L fun s ↦ hgen s
    exact congrArg (fun F : MaximalGroupCStar L →L[ℂ] ℂ ↦ F x) hext

/-! ## The contradiction -/

/-- **`thm:normal-kazhdan`, closing display (tex lines 697-700).**

> So `1 = χ(e_K) = τ(π(e_K)) = τ(0) = 0`, a contradiction. -/
theorem manuscriptSentence_oneEqualsZeroContradiction
    {L : Type} [Group L] (KD : KazhdanData L) {A : Type} [CStarAlgebra A]
    (π : MaximalGroupCStar L →⋆ₐ[ℂ] A) (τ : A →L[ℂ] ℂ)
    (hπe : π KD.projection = 0)
    (hagree : ∀ x : MaximalGroupCStar L,
      τ (π x) = maximalGroupCStarTrivialCharacter L x) :
    False := by
  have h1 : (1 : ℂ) = 0 := by
    calc (1 : ℂ) = maximalGroupCStarTrivialCharacter L KD.projection :=
          (maximalGroupCStarTrivialCharacter_kazhdanProjection KD).symm
      _ = τ (π KD.projection) := (hagree KD.projection).symm
      _ = τ 0 := by rw [hπe]
      _ = 0 := map_zero τ
  exact one_ne_zero h1

/-! ## The endpoint -/

/-- **Theorem `thm:normal-kazhdan`, proved along the printed ultrafilter route.**

The same closed proposition as `manuscriptNormalKazhdanRadical`, proved by the
printed sentences: the Kazhdan projection and its image, normality, the nonzero
central complement, the corner representation, `π(e_K) = 0` in `𝒬_r`, the
ultrafilter trace `τ`, `τ(π(u_k)) = 1`, the trivial character, the agreement of
the two states, and `1 = 0`. -/
theorem manuscriptNormalKazhdanRadical_ultrafilterRoute : NormalKazhdanRadical := by
  classical
  intro G _ _ K _ hT hKres k0 hk0
  show ActualCoronaMFInvisible k0
  intro X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  by_contra hne
  obtain ⟨KD⟩ := exists_kazhdanData ↥K hT
  obtain ⟨f, hf, hpsa, hpid, -⟩ :=
    manuscriptSentence_kazhdanProjectionImage KD (rho.comp K.subtype)
  have hconj : ∀ g : G,
      ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * f KD.projection
        * star ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) = f KD.projection := by
    intro g
    obtain ⟨hc1, hc2⟩ :=
      manuscriptSentence_normalityGivesBothCompressions K rho g
    exact (manuscriptSentence_conjugateFixesKazhdanImage KD
      (rho.comp K.subtype) f hf _
      (Unitary.star_mul_self_of_mem (rho g).2)
      (Unitary.mul_star_self_of_mem (rho g).2) hc1 hc2).1
  obtain ⟨hsp, hzero, -, hqcomm⟩ :=
    manuscriptSentence_complementIsCentralProjection hpsa hpid
      (fun g : G ↦ ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))) hconj
      (fun g ↦ Unitary.star_mul_self_of_mem (rho g).2)
  have hqne : (1 : NormMatrixCStarCorona (fun n ↦ X n)) - f KD.projection ≠ 0 :=
    manuscriptSentence_complementNonzero KD (rho.comp K.subtype) f hf
      (s0 := ⟨k0, hk0⟩) hne
  obtain ⟨φ, hφ, -, D, -, -, -, -, -, -, hclass⟩ :=
    manuscriptCornerCoronaClass G X rho
      ((1 : NormMatrixCStarCorona (fun n ↦ X n)) - f KD.projection)
      hsp.isSelfAdjoint hsp.isIdempotentElem hqne hqcomm
  obtain ⟨π, hπ, -⟩ := maximalGroupCStar_existsUnique_lift_allUniverses ↥K
    ((cornerCoronaUnitaryHom D).comp K.subtype)
  have hπe : π KD.projection = 0 :=
    manuscriptSentence_inducedCornerKazhdanProjectionZero X rho KD f K.subtype hf
      hzero φ hφ D hclass π hπ
  have hτπ := manuscriptSentence_ultrafilterTraceOfInducedGeneratorIsOne K.subtype
    (fun s ↦ hKres s.2) D (Filter.hyperfilter ℕ) Filter.hyperfilter_le_cofinite π hπ
  obtain ⟨-, -, hagree⟩ := manuscriptSentence_statesAgreeOnGeneratorsSpanAndAlgebra π
    (ultrafilterNormalizedTraceCLM (fun n ↦ D.cornerModel n) (Filter.hyperfilter ℕ)
      Filter.hyperfilter_le_cofinite) hτπ
  exact manuscriptSentence_oneEqualsZeroContradiction KD π _ hπe hagree

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_ultrafilterTraceIsTracialStateOnCorona
#audit_axioms
  Manuscript.NonMFSentences.manuscriptSentence_inducedCornerKazhdanProjectionZero
#audit_axioms
  Manuscript.NonMFSentences.manuscriptSentence_ultrafilterTraceOfInducedGeneratorIsOne
#audit_axioms
  Manuscript.NonMFSentences.manuscriptSentence_trivialCharacterIsStateWithValues
#audit_axioms
  Manuscript.NonMFSentences.manuscriptSentence_statesAgreeOnGeneratorsSpanAndAlgebra
#audit_axioms
  Manuscript.NonMFSentences.manuscriptSentence_oneEqualsZeroContradiction
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptNormalKazhdanRadical_ultrafilterRoute
