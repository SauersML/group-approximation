import GroupApproximation.Sofic.OpAlmostRepresentation
import GroupApproximation.Sofic.UltrafilterSubsequence
import GroupApproximation.Sofic.UltraproductModelConstruction

/-!
# KT.01: the contradiction opening, at the printed commutator

The printed proof of the Kazhdan transport result opens:

> Suppose the conclusion fails: there are `γ₀ ∈ Γ`, `δ > 0`, and an infinite set
> `I ⊆ ℕ` with `‖[U_n(s)x_nU_n(s)*, U_n(ι(γ₀))]_-‖ ≥ δ` for `n ∈ I`.  Fix a free
> ultrafilter `ω` on `ℕ` with `I ∈ ω`.

`Sofic/UltrafilterSubsequence.lean` proves the extraction, but for an arbitrary
finite index set and an arbitrary real defect `f n γ`; the proof ledger records
row `KT.01` as MISMATCH for exactly that reason -- "it is stated ... not
instantiated at the printed commutator, so the objects are substituted".

This file supplies the missing instantiation.  `transportedCommutator` is the
printed matrix `[U_n(s)x_nU_n(s)*, U_n(ι(γ))]_-` and `transportedDefect` is its
normalized Hilbert--Schmidt norm at the weight, so the statements below are the
printed sentence with the printed quantity in it.

## Two extractions, and which one the print makes

The printed `γ₀` ranges over `Γ`, and failure of "`→ 0` for every `γ ∈ Γ`"
already yields one `γ₀` with a fixed positive defect on an infinite set: no
pigeonhole is needed, only the negation of a limit
(`kt_01_exists_infinite_defect`).  The finite-generating-set form is genuinely
stronger -- it starts from failure of a bound *uniform over `S`* -- and it is
what `exists_index_infinite_defect` proves; `kt_01_exists_index_infinite_defect`
records that form at the printed defect too, since the Kazhdan set is where a
uniform statement would be taken.
-/

namespace GroupApproximation
namespace OmegaDefectExtraction

open Filter Matrix Topology
open ScaledKazhdanTransport UltrafilterLimit UltraproductModelConstruction

noncomputable section

universe u

/-! ## Failure of a limit, as an infinite set of stages -/

/-- A nonnegative sequence that does not tend to zero exceeds some fixed
positive threshold on an infinite set of stages.  This is the printed step
"there are `δ > 0` and an infinite set `I ⊆ ℕ`". -/
theorem exists_infinite_defect_of_not_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ¬ Tendsto f atTop (𝓝 (0 : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ {n : ℕ | δ ≤ f n}.Infinite := by
  rw [Metric.tendsto_atTop] at h
  push Not at h
  obtain ⟨δ, hδ, hN⟩ := h
  refine ⟨δ, hδ, ?_⟩
  rw [← Nat.frequently_atTop_iff_infinite, Filter.frequently_atTop]
  intro N
  obtain ⟨n, hn, hdist⟩ := hN N
  refine ⟨n, hn, ?_⟩
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hf n)] at hdist

/-! ## The printed commutator and its defect -/

section Printed

variable {Γ : Type*} {H : Type u} [Group Γ] [Group H]
variable (A : OpAlmostRepresentation H) (w : ℕ → ℝ) (iota : Γ →* H) (s : H)
  (x : MatFam A.model)

/-- **The printed matrix `[U_n(s)x_nU_n(s)*, U_n(ι(γ))]_-`.** -/
def transportedCommutator (n : ℕ) (γ : Γ) :
    Matrix (A.model n) (A.model n) ℂ :=
  ((A.map n s : Matrix (A.model n) (A.model n) ℂ) * x n
      * (A.map n s : Matrix (A.model n) (A.model n) ℂ)ᴴ)
    * (A.map n (iota γ) : Matrix (A.model n) (A.model n) ℂ)
  - (A.map n (iota γ) : Matrix (A.model n) (A.model n) ℂ)
    * ((A.map n s : Matrix (A.model n) (A.model n) ℂ) * x n
      * (A.map n s : Matrix (A.model n) (A.model n) ℂ)ᴴ)

/-- **The printed quantity `‖[U_n(s)x_nU_n(s)*, U_n(ι(γ))]_-‖_{2}`**: the
normalized Hilbert--Schmidt norm of the transported commutator at the weight,
i.e. the square root of the renormalized Frobenius mass. -/
def transportedDefect (n : ℕ) (γ : Γ) : ℝ :=
  Real.sqrt (matMass (transportedCommutator A iota s x n γ) / w n)

theorem transportedDefect_nonneg (n : ℕ) (γ : Γ) :
    0 ≤ transportedDefect A w iota s x n γ :=
  Real.sqrt_nonneg _

/-- **KT.01, as printed.**  If the printed conclusion fails -- if it is not the
case that the transported commutator tends to zero in normalized
Hilbert--Schmidt norm for every `γ ∈ Γ` -- then there are `γ₀ ∈ Γ`, a threshold
`δ > 0`, and an infinite set of stages on which the printed commutator stays at
or above `δ`.

This is the opening sentence of the printed proof, with the printed quantity in
place of an abstract defect. -/
theorem kt_01_exists_infinite_defect
    (h : ¬ ∀ γ : Γ,
      Tendsto (fun n ↦ transportedDefect A w iota s x n γ) atTop (𝓝 (0 : ℝ))) :
    ∃ γ₀ : Γ, ∃ δ : ℝ, 0 < δ ∧
      {n : ℕ | δ ≤ transportedDefect A w iota s x n γ₀}.Infinite := by
  push Not at h
  obtain ⟨γ₀, hγ₀⟩ := h
  obtain ⟨δ, hδ, hinf⟩ :=
    exists_infinite_defect_of_not_tendsto
      (fun n ↦ transportedDefect_nonneg A w iota s x n γ₀) hγ₀
  exact ⟨γ₀, δ, hδ, hinf⟩

/-- **KT.01 and KT.02 together, at the printed commutator.**  The failure of the
printed conclusion produces the printed data: a generator `γ₀`, a threshold
`δ > 0`, and a *free* ultrafilter `ω` -- one refining the cofinite filter -- along
which the printed commutator stays at or above `δ`.

This is the object the printed proof hands to the ultraproduct construction. -/
theorem kt_01_exists_freeUltrafilter_defect
    (h : ¬ ∀ γ : Γ,
      Tendsto (fun n ↦ transportedDefect A w iota s x n γ) atTop (𝓝 (0 : ℝ))) :
    ∃ γ₀ : Γ, ∃ δ : ℝ, 0 < δ ∧ ∃ ω : Ultrafilter ℕ,
      (ω : Filter ℕ) ≤ cofinite ∧
        ∀ᶠ n in (ω : Filter ℕ), δ ≤ transportedDefect A w iota s x n γ₀ := by
  obtain ⟨γ₀, δ, hδ, hinf⟩ := kt_01_exists_infinite_defect A w iota s x h
  obtain ⟨ω, hmem, hle⟩ := exists_freeUltrafilter_mem hinf
  exact ⟨γ₀, δ, hδ, ω, hle, hmem⟩

/-- **KT.01 in its uniform form, at the printed commutator.**  Failure of a
bound uniform over a finite set `S ⊆ Γ` -- the Kazhdan set, which is where
property (T) supplies finiteness -- fixes a single `γ₀ ∈ S` carrying a positive
defect on an infinite set of stages.

This is `UltrafilterSubsequence.exists_index_infinite_defect` instantiated at the
printed defect, which is the instantiation the proof ledger records as missing
at row `KT.01`. -/
theorem kt_01_exists_index_infinite_defect (S : Finset Γ)
    (h : ¬ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ γ ∈ S, transportedDefect A w iota s x n γ ≤ ε) :
    ∃ γ₀ ∈ S, ∃ δ : ℝ, 0 < δ ∧
      {n : ℕ | δ ≤ transportedDefect A w iota s x n γ₀}.Infinite :=
  UltrafilterSubsequence.exists_index_infinite_defect S
    (fun n γ ↦ transportedDefect A w iota s x n γ) h

end Printed

end

end OmegaDefectExtraction
end GroupApproximation
