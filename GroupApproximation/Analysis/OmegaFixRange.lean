import GroupApproximation.Analysis.OmegaActionLinear
import GroupApproximation.Analysis.OmegaFiniteComparison

/-!
# `ran P = Fix π(ι Γ)` and `ran Q = Fix π(s ι(Γ) s⁻¹)` in `K_ω`

`Analysis/OmegaFiniteComparison.lean` proves the projection equality
`Q = P` in `B_ω`, from `P ≤ Q`, Murray--von Neumann equivalence and Dedekind
finiteness of the corona.  The printed `htransport`, though, is an equality of
**fixed spaces**, and until now nothing tied either fixed space to the
projection that is supposed to project onto it.  This file supplies exactly
that bridge, in both instances:

* `range_proj_eq_omegaFix` -- `ran P = Fix π(ι Γ)`;
* `range_conjProj_eq_omegaFixConj` -- `ran Q = Fix π(s ι(Γ) s⁻¹)`.

With those two, the printed identification of the fixed spaces is pure
rewriting along `omegaConjProj_eq_proj`, and that is `omegaFixConj_eq_omegaFix`
below.

## Neither range identification uses finiteness

This is the useful part of the factorisation.  Both identifications hold in any
compression bundle over `B_ω`, with no comparison theory at all:

* `ran P ⊆ Fix` is `kt_08_rep_mul_proj`, the absorption `π(ι γ) P = P`;
* `Fix ⊆ ran P` is `OmegaActionLinear.omegaAct_proj_of_fixed`, which is where
  the spectral gap is consumed, through the resolvent factorisation of `1 - P`;
* the two inclusions for `Q` are the same two, conjugated by `V`, together with
  `kt_19_omega_mem_fix_iff` for the direction that identifies the conjugated
  fixed space with `V · Fix`.

Finiteness enters in exactly one place, `omegaConjProj_eq_proj`, and it is the
only place the printed proof spends it either.  Keeping it out of the range
identifications is what makes them reusable for any `s`, including ones for
which `Q ≠ P`.
-/

namespace GroupApproximation
namespace OmegaFixRange

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection OmegaConjugationOperators

noncomputable section

section Range

variable {Γ H : Type} [Group Γ] [Group H]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (ω : Ultrafilter ℕ)
  (w : ℕ → ℝ)

/-- **`Fix π(s ι(Γ) s⁻¹) ⊆ K_ω`**, the fixed space of the conjugated image, as
a subspace.  The companion of `omegaFix`. -/
def omegaFixConj (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    Submodule ℂ (Vec Y w ω) where
  carrier := {ζ | ∀ γ : Γ, omegaAct Y w ω hw
    (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) ζ = ζ}
  zero_mem' := by
    intro γ
    exact map_zero _
  add_mem' := by
    intro x y hx hy γ
    rw [map_add, hx γ, hy γ]
  smul_mem' := by
    intro c x hx γ
    rw [map_smul, hx γ]

theorem mem_omegaFixConj_iff (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω))
    (ζ : Vec Y w ω) :
    ζ ∈ omegaFixConj Y ω w hw D ↔
      ∀ γ : Γ, omegaAct Y w ω hw
        (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) ζ = ζ :=
  Iff.rfl

/-! ## `ran P = Fix π(ι Γ)` -/

/-- **`ran P = Fix π(ι Γ)`**, the printed "the spectral projection `P` … projects
onto `Fix`", as an equality of subspaces of `K_ω`.

No finiteness and no comparison theory: the inclusion `⊆` is the absorption
`π(ι γ) P = P`, and `⊇` is the spectral-gap step. -/
theorem range_proj_eq_omegaFix (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    LinearMap.range (omegaAct Y w ω hw D.proj) = omegaFix Y ω w hw D := by
  apply le_antisymm
  · rintro ζ ⟨x, rfl⟩
    refine (mem_omegaFix_iff Y ω w hw D _).2 fun γ ↦ ?_
    have hrep : omegaRep Y ω D (D.iota γ) * D.proj = D.proj :=
      D.kt_08_rep_mul_proj γ
    calc omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ))
            (omegaAct Y w ω hw D.proj x)
        = omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ) * D.proj) x := by
          rw [omegaAct_mul]
      _ = omegaAct Y w ω hw D.proj x := by rw [hrep]
  · intro ζ hζ
    refine ⟨ζ, ?_⟩
    exact OmegaActionLinear.omegaAct_proj_of_fixed Y w ω hw D
      ((mem_omegaFix_iff Y ω w hw D ζ).1 hζ)

/-! ## `ran Q = Fix π(s ι(Γ) s⁻¹)` -/

/-- **`ran Q = Fix π(s ι(Γ) s⁻¹)`**, the printed "its conjugate `Q = π(s) P π(s)*`,
whose range is `Fix π(sLs⁻¹)`".

Again finiteness-free.  The inclusion `⊆` conjugates the absorption by `V`; the
inclusion `⊇` runs `kt_19_omega_mem_fix_iff` to put `V* η` in `Fix`, applies the
spectral-gap step there, and conjugates back. -/
theorem range_conjProj_eq_omegaFixConj (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    LinearMap.range (omegaAct Y w ω hw (omegaConjProj Y ω D))
      = omegaFixConj Y ω w hw D := by
  have hVV : D.shift * star D.shift = 1 := D.shift_mul_star
  have hVsV : star D.shift * D.shift = 1 := D.shift_star_mul
  apply le_antisymm
  · rintro ζ ⟨x, rfl⟩
    refine (mem_omegaFixConj_iff Y ω w hw D _).2 fun γ ↦ ?_
    -- `π(s ι γ s⁻¹) Q = Q`, by conjugating `π(ι γ) P = P`
    have hrep : omegaRep Y ω D (D.iota γ) * D.proj = D.proj :=
      D.kt_08_rep_mul_proj γ
    have hconj : omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)
        * omegaConjProj Y ω D = omegaConjProj Y ω D := by
      rw [← omegaRep_conj, omegaConjProj_def]
      calc D.shift * omegaRep Y ω D (D.iota γ) * star D.shift
            * (D.shift * D.proj * star D.shift)
          = D.shift * omegaRep Y ω D (D.iota γ)
              * (star D.shift * D.shift) * D.proj * star D.shift := by
            noncomm_ring
        _ = D.shift * omegaRep Y ω D (D.iota γ) * 1 * D.proj
              * star D.shift := by rw [hVsV]
        _ = D.shift * (omegaRep Y ω D (D.iota γ) * D.proj)
              * star D.shift := by noncomm_ring
        _ = D.shift * D.proj * star D.shift := by rw [hrep]
    calc omegaAct Y w ω hw (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹))
            (omegaAct Y w ω hw (omegaConjProj Y ω D) x)
        = omegaAct Y w ω hw (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)
            * omegaConjProj Y ω D) x := by rw [omegaAct_mul]
      _ = omegaAct Y w ω hw (omegaConjProj Y ω D) x := by rw [hconj]
  · intro η hη
    refine ⟨η, ?_⟩
    -- `V* η` lies in `Fix`, so `P` fixes it
    have hmem : omegaAct Y w ω hw (star D.shift) η ∈ omegaFix Y ω w hw D :=
      (kt_19_omega_mem_fix_iff Y ω w hw D η).1
        ((mem_omegaFixConj_iff Y ω w hw D η).1 hη)
    have hP : omegaAct Y w ω hw D.proj
          (omegaAct Y w ω hw (star D.shift) η)
        = omegaAct Y w ω hw (star D.shift) η :=
      OmegaActionLinear.omegaAct_proj_of_fixed Y w ω hw D
        ((mem_omegaFix_iff Y ω w hw D _).1 hmem)
    calc omegaAct Y w ω hw (omegaConjProj Y ω D) η
        = omegaAct Y w ω hw (D.shift * D.proj * star D.shift) η := by
          rw [omegaConjProj_def]
      _ = omegaAct Y w ω hw D.shift
            (omegaAct Y w ω hw D.proj
              (omegaAct Y w ω hw (star D.shift) η)) := by
          rw [omegaAct_mul, omegaAct_mul]
      _ = omegaAct Y w ω hw D.shift
            (omegaAct Y w ω hw (star D.shift) η) := by rw [hP]
      _ = omegaAct Y w ω hw (D.shift * star D.shift) η := by rw [omegaAct_mul]
      _ = η := by rw [hVV, omegaAct_one]

/-! ## `htransport`, by rewriting -/

/-- **The printed `htransport`.**  `Fix π(s ι(Γ) s⁻¹) = Fix π(ι Γ)` inside
`K_ω`.

The two fixed spaces are the ranges of `Q` and of `P` by the identifications
above, and `Q = P` is `OmegaFiniteComparison.omegaConjProj_eq_proj`.  So the
printed statement is a rewrite, and every analytic input sits in one of the
three cited theorems rather than here. -/
theorem omegaFixConj_eq_omegaFix (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    omegaFixConj Y ω w hw D = omegaFix Y ω w hw D := by
  rw [← range_conjProj_eq_omegaFixConj Y ω w hw D,
    ← range_proj_eq_omegaFix Y ω w hw D,
    OmegaFiniteComparison.omegaConjProj_eq_proj Y ω D]

/-- **`htransport` in the implication shape the collapse endpoint consumes.**
Every vector fixed by the conjugated image is fixed by the original one. -/
theorem fix_of_fix_conjugated (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω))
    {η : Vec Y w ω}
    (hη : ∀ γ : Γ, omegaAct Y w ω hw
        (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) η = η) :
    ∀ γ : Γ, omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ)) η = η := by
  have hmem : η ∈ omegaFix Y ω w hw D := by
    rw [← omegaFixConj_eq_omegaFix Y ω w hw D]
    exact (mem_omegaFixConj_iff Y ω w hw D η).2 hη
  exact (mem_omegaFix_iff Y ω w hw D η).1 hmem

end Range

end

end OmegaFixRange
end GroupApproximation
