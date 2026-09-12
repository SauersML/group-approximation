import GroupApproximation.Leavitt.FullIdempotentNormalGeneration
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# The compressor at every rank `n ≥ 4`

`non_mf_groups_exist.tex`, Section `sec:one-sided-inverses`, the standing
convention of the proof of Theorem `thm:full-defect-ring`:

> Put `G = EL_n(R)` and let `L = EL₃(R)` occupy coordinates `1,2,3`. …
> All displayed `4×4` matrices below are extended by `I_{n-4}`.

That sentence is a block embedding `EL₄(R) → EL_n(R)`, and this module is it.
Everything printed at rank four — the core `L`, the compressor `u`, the
centralizer element `c`, the core element `ℓ` and the defect `d` — is the
image of its rank-four namesake under `blockEmbedding`, and the printed
compression, commutation and Steinberg identities transport along the
homomorphism verbatim.  Nothing new is computed here.

The one statement that does not transport is `𝔇_G(L) = ⊤`: it is proved again
at rank `n` from the *rank-`n`* normal-generation theorem of
`Leavitt.FullIdempotentNormalGeneration`, whose hypothesis `4 ≤ n` is the
printed rank restriction.

The closed printed endpoint carried here is
`PrintedFullDefectSaturation`: for every unital ring with a one-sided inverse
pair whose complementary idempotent is full, and every `n ≥ 4`, the printed
defect of the core inside `EL_n(R)` is everything.  That is the algebraic core
of Theorem `thm:full-defect-ring`; the operator-algebraic conclusion drawn from
it is `Manuscript.OneSidedMFRadical.FullDefectRing`.
-/

namespace GroupApproximation
namespace OneSidedCompressor

open scoped commutatorElement

universe u w

variable {R : Type u} [Ring R] {n : ℕ}

/-! ### The block embedding `EL₄(R) → EL_n(R)` -/

/-- The printed "extend by `I_{n-4}`" reindexing. -/
def blockIndexEquiv (hn : 4 ≤ n) : Fin 4 ⊕ Fin (n - 4) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The four compressor coordinates inside `Fin n`. -/
def bigIdx (hn : 4 ≤ n) (i : Fin 4) : Fin n := blockIndexEquiv hn (Sum.inl i)

theorem bigIdx_injective (hn : 4 ≤ n) : Function.Injective (bigIdx hn) :=
  fun _ _ h ↦ Sum.inl_injective ((blockIndexEquiv hn).injective h)

/-- The block inclusion `EL₄(R) → EL_n(R)` of the printed convention. -/
noncomputable def blockEmbedding (hn : 4 ≤ n) :
    elementaryGroup (Fin 4) R →* elementaryGroup (Fin n) R :=
  (elementaryReindexEquiv (R := R) (blockIndexEquiv hn)).toMonoidHom.comp
    (elementaryStabilization (ι := Fin 4) (κ := Fin (n - 4)) (R := R))

@[simp] theorem blockEmbedding_elementaryRoot (hn : 4 ≤ n)
    (i j : Fin 4) (hij : i ≠ j) (a : R) :
    blockEmbedding (R := R) hn (elementaryRoot i j hij a) =
      elementaryRoot (bigIdx hn i) (bigIdx hn j)
        ((bigIdx_injective hn).ne hij) a := by
  apply Subtype.ext
  change elementaryReindexUnitEquiv (R := R) (blockIndexEquiv hn)
      (stabilizeUnit (κ := Fin (n - 4)) (elementaryUnit i j hij a)) =
    elementaryUnit (bigIdx hn i) (bigIdx hn j) ((bigIdx_injective hn).ne hij) a
  rw [stabilizeUnit_elementaryUnit, elementaryReindexUnitEquiv_elementaryUnit]
  rfl

theorem blockEmbedding_injective (hn : 4 ≤ n) :
    Function.Injective (blockEmbedding (R := R) hn) :=
  (elementaryReindexEquiv (R := R) (blockIndexEquiv hn)).injective.comp
    elementaryStabilization_injective

/-! ### The printed data at rank `n` -/

/-- The printed core `L = EL₃(R)`, occupying coordinates `1,2,3` of
`EL_n(R)`. -/
noncomputable def coreOf (R : Type u) [Ring R] {n : ℕ} (hn : 4 ≤ n) :
    Subgroup (elementaryGroup (Fin n) R) :=
  (core R).map (blockEmbedding (R := R) hn)

/-- The printed compressor `u`, extended by `I_{n-4}`. -/
noncomputable def compressorOf (P : OneSidedInverse R) (hn : 4 ≤ n) :
    elementaryGroup (Fin n) R :=
  blockEmbedding hn (compressor P)

/-- The printed centralizer element `c`, extended by `I_{n-4}`. -/
noncomputable def centralMarkOf (P : OneSidedInverse R) (hn : 4 ≤ n) :
    elementaryGroup (Fin n) R :=
  blockEmbedding hn (centralMark P)

/-- The printed core element `ℓ = e₂₃(1)`, extended by `I_{n-4}`. -/
noncomputable def printedEllOf (R : Type u) [Ring R] {n : ℕ} (hn : 4 ≤ n) :
    elementaryGroup (Fin n) R :=
  blockEmbedding (R := R) hn (printedEll R)

/-- The printed defect element `d = e₁₃(e)`, extended by `I_{n-4}`. -/
noncomputable def printedDefectRootOf (P : OneSidedInverse R) (hn : 4 ≤ n) :
    elementaryGroup (Fin n) R :=
  blockEmbedding hn (printedDefectRoot P)

/-! ### The printed identities, transported -/

theorem elementaryRoot_mem_coreOf (hn : 4 ≤ n) (i j : Fin 3) (hij : i ≠ j)
    (a : R) :
    elementaryRoot (bigIdx hn (coreIdx i)) (bigIdx hn (coreIdx j))
        ((bigIdx_injective hn).ne (coreIdx_injective.ne hij)) a ∈ coreOf R hn := by
  refine ⟨elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a,
    elementaryRoot_mem_core i j hij a, ?_⟩
  rw [blockEmbedding_elementaryRoot]

/-- **`u L u⁻¹ ≤ L` at rank `n`.** -/
theorem compressorOf_compresses_coreOf (P : OneSidedInverse R) (hn : 4 ≤ n) :
    ∀ g ∈ coreOf R hn,
      compressorOf P hn * g * (compressorOf P hn)⁻¹ ∈ coreOf R hn := by
  rintro _ ⟨δ, hδ, rfl⟩
  exact ⟨compressor P * δ * (compressor P)⁻¹, compressor_compresses_core P δ hδ,
    by simp [compressorOf]⟩

theorem compressorOf_mem_compressionSet (P : OneSidedInverse R) (hn : 4 ≤ n) :
    compressorOf P hn ∈ compressionSet (coreOf R hn) :=
  compressorOf_compresses_coreOf P hn

/-- **`c ∈ C_G(L)` at rank `n`.** -/
theorem centralMarkOf_commute_coreOf (P : OneSidedInverse R) (hn : 4 ≤ n) :
    ∀ g ∈ coreOf R hn, Commute (centralMarkOf P hn) g := by
  rintro _ ⟨δ, hδ, rfl⟩
  have h := centralMark_commute_core P δ hδ
  show centralMarkOf P hn * blockEmbedding hn δ =
    blockEmbedding hn δ * centralMarkOf P hn
  rw [centralMarkOf, ← map_mul, ← map_mul, h.eq]

theorem printedEllOf_mem_coreOf (hn : 4 ≤ n) :
    printedEllOf R hn ∈ coreOf R hn :=
  ⟨printedEll R, printedEll_mem_core, rfl⟩

/-- **The printed defect equation `d = [ucu⁻¹, ℓ]` at rank `n`.** -/
theorem defectOf_eq (P : OneSidedInverse R) (hn : 4 ≤ n) :
    ⁅compressorOf P hn * centralMarkOf P hn * (compressorOf P hn)⁻¹,
        printedEllOf R hn⁆ = printedDefectRootOf P hn := by
  have h : blockEmbedding (R := R) hn
      ⁅compressor P * centralMark P * (compressor P)⁻¹, printedEll R⁆
      = printedDefectRootOf P hn := by
    rw [defect_eq]
    rfl
  rw [← h]
  simp [compressorOf, centralMarkOf, printedEllOf, commutatorElement_def]

/-- **The defect membership at rank `n`.** -/
theorem printedDefectRootOf_mem_printedDefect (P : OneSidedInverse R)
    (hn : 4 ≤ n) :
    printedDefectRootOf P hn ∈
      Manuscript.OneSidedMFRadical.printedDefect (coreOf R hn) := by
  rw [← defectOf_eq P hn]
  exact Manuscript.OneSidedMFRadical.printedDefect_generator_mem (coreOf R hn)
    (compressorOf_compresses_coreOf P hn) (centralMarkOf_commute_coreOf P hn)
    (printedEllOf_mem_coreOf hn)

/-! ### Saturation of the printed defect -/

/-- **`𝔇_G(L) = ⊤` at every rank `n ≥ 4`.**  This is the group-theoretic
conclusion of the proof of Theorem `thm:full-defect-ring`, before the
compression criterion is applied to it. -/
theorem printedDefectOf_eq_top (P : OneSidedInverse R) (hn : 4 ≤ n)
    (hfull : ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * P.e * b k = 1) :
    Manuscript.OneSidedMFRadical.printedDefect (coreOf R hn) = ⊤ := by
  have h := printedDefectRootOf_mem_printedDefect P hn
  simp only [printedDefectRootOf, printedDefectRoot,
    blockEmbedding_elementaryRoot] at h
  exact FullIdempotent.elementaryGroup_normal_eq_top_of_full (by simpa using hn) _
    ((bigIdx_injective hn).ne (coreIdx_injective.ne zeroNeTwo)) h hfull

/-! ### The core at rank `n` as the image of `EL₃(R)` -/

/-- The upper-left embedding `EL₃(R) → EL_n(R)`. -/
noncomputable def coreEmbeddingOf (hn : 4 ≤ n) :
    elementaryGroup (Fin 3) R →* elementaryGroup (Fin n) R :=
  (blockEmbedding (R := R) hn).comp coreEmbedding

theorem coreEmbeddingOf_range (hn : 4 ≤ n) :
    (coreEmbeddingOf (R := R) hn).range = coreOf R hn := by
  rw [coreEmbeddingOf, MonoidHom.range_comp, coreEmbedding_range, coreOf]

/-- The upper-left embedding, corestricted to the core. -/
noncomputable def coreEmbeddingOfToCore (hn : 4 ≤ n) :
    elementaryGroup (Fin 3) R →* (coreOf R hn) :=
  (coreEmbeddingOf (R := R) hn).codRestrict (coreOf R hn) fun g ↦ by
    rw [← coreEmbeddingOf_range]
    exact ⟨g, rfl⟩

theorem coreEmbeddingOfToCore_surjective (hn : 4 ≤ n) :
    Function.Surjective (coreEmbeddingOfToCore (R := R) hn) := by
  intro x
  have hx : (x : elementaryGroup (Fin n) R) ∈
      (coreEmbeddingOf (R := R) hn).range := by
    rw [coreEmbeddingOf_range]
    exact x.property
  obtain ⟨g, hg⟩ := hx
  exact ⟨g, Subtype.ext hg⟩

/-- **Property `(T)` for the core at rank `n`**, from property `(T)` of
`EL₃(R)`.  This is the printed "three for the subgroup `EL₃(R)`, which has
property `(T)` once `R` is replaced by a finitely generated unital subring". -/
theorem coreOf_hasKazhdanPropertyT (hn : 4 ≤ n)
    (h : HasKazhdanPropertyT.{u, w} (elementaryGroup (Fin 3) R)) :
    HasKazhdanPropertyT.{u, w} (coreOf R hn) :=
  HasKazhdanPropertyT.of_surjective (coreEmbeddingOfToCore hn)
    (coreEmbeddingOfToCore_surjective hn) h

/-! ### The closed printed endpoint -/

/-- **The algebraic core of Theorem `thm:full-defect-ring`.**  For every unital
ring carrying a one-sided inverse pair `t s = 1` whose complementary idempotent
`e = 1 - st` is full in the printed sense `∑_j a_j e b_j = 1`, and every rank
`n ≥ 4`, the printed defect `𝔇_G(L)` of the core `L = EL₃(R)` inside
`G = EL_n(R)` is all of `G`. -/
def PrintedFullDefectSaturation : Prop :=
  ∀ {S : Type*} [Ring S] (P : OneSidedInverse S) {n : ℕ} (hn : 4 ≤ n),
    (∃ (m : ℕ) (a b : Fin m → S), ∑ k, a k * P.e * b k = 1) →
      Manuscript.OneSidedMFRadical.printedDefect (coreOf S hn) = ⊤

theorem manuscriptPrintedFullDefectSaturation : PrintedFullDefectSaturation := by
  intro S _ P n hn hfull
  exact printedDefectOf_eq_top P hn hfull

end OneSidedCompressor
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  OneSidedCompressor.manuscriptPrintedFullDefectSaturation
