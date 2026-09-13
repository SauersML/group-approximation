import GroupApproximation.Analysis.MaximalCStarProperCompression
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing

/-!
# `uPu*` is the Kazhdan projection of `tΓt⁻¹`

`non_mf_groups_exist.tex`, proof of Proposition `prop:max-infinite` (`\label{prop:max-infinite}`, tex lines 755–759 at
origin/main 68481e4d7):

> Conjugation by `u` implements the isomorphism `Γ → tΓt⁻¹` on canonical unitaries, so by
> Lemma `lem:kazhdan-projection-order` applied with `U = u`, `P ≤ uPu*`, where `uPu*` is the image of the Kazhdan
> projection of `tΓt⁻¹`.

The order `P ≤ uPu*` is `StrictKazhdanCompression.conjugate_mul_proj` and `proj_mul_conjugate`.  This file carries the
two remaining clauses.

* `shift_mul_rep_mul_star_shift`: conjugation by `u = u_t` sends the canonical unitary of `ι(γ)` to the canonical
  unitary of `t ι(γ) t⁻¹`, an element of `tΓt⁻¹` (`conj_mem_conjLambda`).
* `shift_mul_proj_mul_star_shift`: `uPu*` is the spectral projection, at the same rate, of the average of the canonical
  unitaries of `tΓt⁻¹` over the conjugated Kazhdan set.  That average has the spectral gap (`conjRep_gap`), its
  projection is a star projection (`conjProjection_isStarProjection`), and every canonical unitary of `tΓt⁻¹` fixes it
  (`conjRep_mul_conjProjection`).  So it is the Kazhdan projection of `tΓt⁻¹` inside `C*_max(G)`, built exactly as `P`
  is built for `Γ` (`StrictKazhdanCompression.proj`).

The equality needs no functional-calculus naturality.  Both projections have complements that factor through
`1 - u M u*`, and each factorisation kills the other projection, as in
`MaximalCStarKazhdanProjection.image_eq_spectralProjection`.
-/

namespace GroupApproximation
namespace MaxInfiniteConjugateKazhdanProjection

open AbstractSpectralGap CStarSpectralProjection KazhdanProjectionAbsorption
open MaximalCStarProperCompression

noncomputable section

universe u w

/-- **Spectral projections are natural under unitary conjugation**, for a gapped self-adjoint element.  The
hypotheses are the gap of `m` and of `u m u*` at the same rate; no functional-calculus naturality is used. -/
theorem unitary_conj_spectralProjection {A : Type*} [CStarAlgebra A] {m u : A} {c : ℝ}
    (hm : IsSelfAdjoint m) (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ m, μ ≤ c ∨ μ = 1)
    (hgap' : ∀ μ ∈ spectrum ℝ (u * m * star u), μ ≤ c ∨ μ = 1)
    (h1 : star u * u = 1) (h2 : u * star u = 1) :
    u * spectralProjection m c * star u = spectralProjection (u * m * star u) c := by
  have hM'sa : IsSelfAdjoint (u * m * star u) := hm.conjugate u
  have hmP : m * spectralProjection m c = spectralProjection m c :=
    mul_spectralProjection m hm hc hgap
  -- `(1 - u m u*)` kills `u P u*`
  have hA : ((1 : A) - u * m * star u) * (u * spectralProjection m c * star u) = 0 := by
    calc ((1 : A) - u * m * star u) * (u * spectralProjection m c * star u)
        = u * spectralProjection m c * star u
            - u * m * (star u * u) * spectralProjection m c * star u := by noncomm_ring
      _ = u * spectralProjection m c * star u
            - u * (m * spectralProjection m c) * star u := by rw [h1]; noncomm_ring
      _ = 0 := by rw [hmP, sub_self]
  -- so the spectral projection of `u m u*` absorbs `u P u*`
  have hB : spectralProjection (u * m * star u) c * (u * spectralProjection m c * star u)
      = u * spectralProjection m c * star u := by
    have h : ((1 : A) - spectralProjection (u * m * star u) c)
        * (u * spectralProjection m c * star u) = 0 := by
      rw [one_sub_spectralProjection_eq (u * m * star u) hM'sa hc hgap', mul_assoc, hA, mul_zero]
    rw [sub_mul, one_mul] at h
    exact (sub_eq_zero.mp h).symm
  -- `(1 - u m u*)` kills the spectral projection of `u m u*`
  have hC : ((1 : A) - u * m * star u) * spectralProjection (u * m * star u) c = 0 := by
    rw [sub_mul, one_mul, mul_spectralProjection (u * m * star u) hM'sa hc hgap', sub_self]
  -- the complement of `u P u*` factors through `1 - u m u*`
  obtain ⟨X, hX⟩ : ∃ X : A, (1 : A) - spectralProjection m c = X * ((1 : A) - m) :=
    ⟨_, one_sub_spectralProjection_eq m hm hc hgap⟩
  have hfac : (1 : A) - u * spectralProjection m c * star u
      = (u * X * star u) * ((1 : A) - u * m * star u) := by
    calc (1 : A) - u * spectralProjection m c * star u
        = u * star u - u * spectralProjection m c * star u := by rw [h2]
      _ = u * ((1 : A) - spectralProjection m c) * star u := by noncomm_ring
      _ = u * (X * ((1 : A) - m)) * star u := by rw [hX]
      _ = u * X * star u - u * X * (star u * u) * m * star u := by
        rw [h1]; noncomm_ring
      _ = (u * X * star u) * ((1 : A) - u * m * star u) := by noncomm_ring
  have hD : (u * spectralProjection m c * star u) * spectralProjection (u * m * star u) c
      = spectralProjection (u * m * star u) c := by
    have h : ((1 : A) - u * spectralProjection m c * star u)
        * spectralProjection (u * m * star u) c = 0 := by
      rw [hfac, mul_assoc, hC, mul_zero]
    rw [sub_mul, one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hQsa : IsSelfAdjoint (u * spectralProjection m c * star u) :=
    (isSelfAdjoint_spectralProjection m).conjugate u
  have hP2sa : IsSelfAdjoint (spectralProjection (u * m * star u) c) :=
    isSelfAdjoint_spectralProjection _
  have hstar := congrArg star hB
  rw [star_mul, hP2sa.star_eq, hQsa.star_eq] at hstar
  exact hstar.symm.trans hD

variable {Γ : Type w} {E : Type u} [Group Γ] [Group E]

-- The spectral gap and absorption lemmas are stated over a C*-order; this is the one
-- `MaximalCStarProperCompression` uses.  No statement below mentions the order.
local instance : PartialOrder (MaximalGroupCStar E) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (MaximalGroupCStar E) :=
  CStarAlgebra.spectralOrderedRing _

/-- The canonical unitaries of `tΓt⁻¹` in `C*_max(E)`, indexed by `Γ` through `γ ↦ t ι(γ) t⁻¹`. -/
def conjRep (D : StrictKazhdanCompression Γ E) : Γ →* unitary (MaximalGroupCStar E) :=
  (maximalGroupCStarUnitaryHom E).comp ((MulAut.conj D.t).toMonoidHom.comp D.iota)

/-- **Conjugation by `u` implements `Γ → tΓt⁻¹` on canonical unitaries.** -/
theorem shift_mul_rep_mul_star_shift (D : StrictKazhdanCompression Γ E) (γ : Γ) :
    D.shift * ((D.rep γ : unitary (MaximalGroupCStar E)) : MaximalGroupCStar E) * star D.shift
      = ((conjRep D γ : unitary (MaximalGroupCStar E)) : MaximalGroupCStar E) :=
  D.shift_generator_conj (D.iota γ)

/-- Conjugation by `u` carries the average of `Γ` to the average of `tΓt⁻¹` over the conjugated Kazhdan set. -/
theorem shift_mul_avg_mul_star_shift (D : StrictKazhdanCompression Γ E) :
    D.shift * D.avg * star D.shift = unitaryAverage (conjRep D) D.S := by
  unfold StrictKazhdanCompression.avg unitaryAverage
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun γ _ ↦ D.shift_generator_conj (D.iota γ)

/-- The average of `tΓt⁻¹` has the Kazhdan spectral gap at the rate of `P`. -/
theorem conjRep_gap (D : StrictKazhdanCompression Γ E) :
    ∀ μ ∈ spectrum ℝ (unitaryAverage (conjRep D) D.S), μ ≤ D.rate ∨ μ = 1 := by
  intro μ hμ
  by_cases hμ1 : μ = 1
  · exact Or.inr hμ1
  · left
    have hμℂ : (μ : ℂ) ∈ spectrum ℂ (unitaryAverage (conjRep D) D.S) := by
      have h := spectrum.algebraMap_mem ℂ hμ
      rwa [show (algebraMap ℝ ℂ) μ = (μ : ℂ) by simp] at h
    exact unitaryAverage_spectrum_le (conjRep D) D.kazhdan D.S D.QS D.one_mem
      D.symm D.eps_le hμℂ hμ1

theorem isSelfAdjoint_conjAverage (D : StrictKazhdanCompression Γ E) :
    IsSelfAdjoint (unitaryAverage (conjRep D) D.S) :=
  isSelfAdjoint_unitaryAverage (conjRep D) D.symm

/-- The Kazhdan projection of `tΓt⁻¹` is a star projection. -/
theorem conjProjection_isStarProjection (D : StrictKazhdanCompression Γ E) :
    IsStarProjection (spectralProjection (unitaryAverage (conjRep D) D.S) D.rate) :=
  ⟨isIdempotentElem_spectralProjection _ (isSelfAdjoint_conjAverage D) D.rate_lt_one
      (conjRep_gap D),
    isSelfAdjoint_spectralProjection _⟩

/-- Every canonical unitary of `tΓt⁻¹` fixes its Kazhdan projection. -/
theorem conjRep_mul_conjProjection (D : StrictKazhdanCompression Γ E) (γ : Γ) :
    ((conjRep D γ : unitary (MaximalGroupCStar E)) : MaximalGroupCStar E)
        * spectralProjection (unitaryAverage (conjRep D) D.S) D.rate
      = spectralProjection (unitaryAverage (conjRep D) D.S) D.rate := by
  have hsa := isSelfAdjoint_conjAverage D
  have hfix := unitary_mul_eq_of_average_absorbs (conjRep D) D.symm
    (isSelfAdjoint_spectralProjection _)
    (isIdempotentElem_spectralProjection _ hsa D.rate_lt_one (conjRep_gap D))
    (mul_spectralProjection _ hsa D.rate_lt_one (conjRep_gap D))
    (spectralProjection_mul _ hsa D.rate_lt_one (conjRep_gap D))
  have hγ : γ ∈ Subgroup.closure (D.S : Set Γ) := by
    rw [D.generates]
    trivial
  exact unitary_mul_eq_of_closure (conjRep D) hfix hγ

/-- **`uPu*` is the Kazhdan projection of `tΓt⁻¹`.** -/
theorem shift_mul_proj_mul_star_shift (D : StrictKazhdanCompression Γ E) :
    D.shift * D.proj * star D.shift
      = spectralProjection (unitaryAverage (conjRep D) D.S) D.rate := by
  have hgap' := conjRep_gap D
  rw [← shift_mul_avg_mul_star_shift D] at hgap' ⊢
  exact unitary_conj_spectralProjection D.isSelfAdjoint_avg D.rate_lt_one D.gap hgap'
    D.shift_star_mul D.shift_mul_star

/-- **The printed clauses of tex lines 755–759, as one closed proposition.**

For strict Kazhdan compression data (`StrictKazhdanCompression`, the datum that
`MaximalCStarPrintedHypotheses.exists_strictKazhdanCompression` builds from the printed hypotheses):

1. conjugation by `u = u_t` sends each canonical unitary of `Γ` to the canonical unitary of `t ι(γ) t⁻¹`;
2. those elements lie in `tΓt⁻¹`;
3. the average of the canonical unitaries of `tΓt⁻¹` over the conjugated Kazhdan set has the Kazhdan gap;
4. its spectral projection is a star projection;
5. every canonical unitary of `tΓt⁻¹` fixes it;
6. `uPu*` equals it: `uPu*` is the Kazhdan projection of `tΓt⁻¹`. -/
def PrintedConjugateKazhdanProjection : Prop :=
  ∀ {Γ : Type w} {E : Type u} [Group Γ] [Group E] (D : StrictKazhdanCompression Γ E),
    (∀ γ : Γ, D.shift * ((D.rep γ : unitary (MaximalGroupCStar E)) : MaximalGroupCStar E)
        * star D.shift = ((conjRep D γ : unitary (MaximalGroupCStar E)) : MaximalGroupCStar E)) ∧
      (∀ γ : Γ, D.t * D.iota γ * D.t⁻¹ ∈ D.iota.range.map (MulAut.conj D.t).toMonoidHom) ∧
      (∀ μ ∈ spectrum ℝ (unitaryAverage (conjRep D) D.S), μ ≤ D.rate ∨ μ = 1) ∧
      IsStarProjection (spectralProjection (unitaryAverage (conjRep D) D.S) D.rate) ∧
      (∀ γ : Γ, ((conjRep D γ : unitary (MaximalGroupCStar E)) : MaximalGroupCStar E)
          * spectralProjection (unitaryAverage (conjRep D) D.S) D.rate
        = spectralProjection (unitaryAverage (conjRep D) D.S) D.rate) ∧
      D.shift * D.proj * star D.shift
        = spectralProjection (unitaryAverage (conjRep D) D.S) D.rate

theorem manuscriptConjugateKazhdanProjection : PrintedConjugateKazhdanProjection.{u, w} := by
  intro Γ E _ _ D
  exact ⟨shift_mul_rep_mul_star_shift D, fun γ ↦ D.conj_mem_conjLambda γ, conjRep_gap D,
    conjProjection_isStarProjection D, conjRep_mul_conjProjection D,
    shift_mul_proj_mul_star_shift D⟩

end

end MaxInfiniteConjugateKazhdanProjection
end GroupApproximation

open GroupApproximation

#audit_axioms MaxInfiniteConjugateKazhdanProjection.unitary_conj_spectralProjection
#audit_axioms MaxInfiniteConjugateKazhdanProjection.shift_mul_proj_mul_star_shift
#audit_closed_axioms MaxInfiniteConjugateKazhdanProjection.manuscriptConjugateKazhdanProjection
