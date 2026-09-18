import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowCanonical
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabVec
import GroupApproximation.Algebra.ElementaryPaddingInjective
import GroupApproximation.Meta.AxiomGuard

/-!
# Reading `(v, g)` back from `vdkRowPar (v, g)`

Lane `bh-met-70c`.  Over an arbitrary ring `R`, this formalizes the direction of the
equivalence that `ElemFPK2VdKRowEndpoint` left informal: injectivity of
`K₂(n, R) → K₂(n+1, R)` gives injectivity of the parabolic map
`vdkRowPar : R^n × St_n(R) → St_{n+1}(R)`, `(v, g) ↦ colVec v · stab g`.

* `vdkRowParInj_padCol_eq_colVec`: the two column products `padCol` (from `PaddedCentral`) and
  `colVec` (from `RowColumn`) agree.  Both are additive in `v` and agree on `Pi.single`.
* `vdkRowParInj_padMat_mulVec`: the matrix of `vdkRowPar (v, g)` sends `(0, 1)` to `(v, 1)`.
  Its matrix is `[[M_g, v], [0, 1]]`.
* `vdkRowParInj_fst_eq`, `vdkRowParInj_stab_eq`: equal images force `v = v'`, and then
  `stab g = stab g'` after cancelling `colVec v`.
* `vdkRowParInj_eq_of_stab_eq`: if `K2Stab` is injective, `stab g = stab g'` forces `g = g'`.
  Here `u = g g'⁻¹` has `stab u = 1`.  So `elementaryStab (projection u) = 1`, and the identity
  padding is injective (`elementaryPad_injective`), so `u ∈ K₂(n, R)`.  Then `K2Stab u = 1`.
* `vdkRowParInjective_of_K2Stab_injective`: the resulting implication.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
  (colVec colVec_add colVec_zero)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
  (padCol padMat padCol_add padCol_zero padCol_single)
open GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
  (surjStabVec surjStabVec_inj surjStab_stab_mulVec surjStab_padCol_mulVec_one)
open scoped Matrix

variable {R : Type*} [Ring R] {n : ℕ}

/-- `padCol v = colVec v`: both are the product `∏ᵢ x_{i,last}(vᵢ)`. -/
theorem vdkRowParInj_padCol_eq_colVec (v : Fin n → R) : padCol v = colVec v := by
  induction v using Pi.single_induction with
  | zero => rw [padCol_zero, colVec_zero]
  | add f g hf hg => rw [padCol_add, colVec_add, hf, hg]
  | single p a =>
    rw [padCol_single, vdkRow_colVec_single]
    rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInj_padCol_eq_colVec

/-- The matrix of `vdkRowPar (v, g)` sends `(0, 1)` to `(v, 1)`. -/
theorem vdkRowParInj_padMat_mulVec (v : Fin n → R) (g : St n R) :
    padMat (vdkRowPar (v, g)) *ᵥ surjStabVec 0 1 = surjStabVec v 1 := by
  rw [vdkRowPar_apply, ← vdkRowParInj_padCol_eq_colVec, map_mul padMat (padCol v) (stab n R g),
    ← Matrix.mulVec_mulVec, surjStab_stab_mulVec, Matrix.mulVec_zero,
    surjStab_padCol_mulVec_one, zero_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInj_padMat_mulVec

/-- Equal images under `vdkRowPar` have equal column parameters. -/
theorem vdkRowParInj_fst_eq {v v' : Fin n → R} {g g' : St n R}
    (h : vdkRowPar (v, g) = vdkRowPar (v', g')) : v = v' := by
  have e := vdkRowParInj_padMat_mulVec v g
  rw [h, vdkRowParInj_padMat_mulVec] at e
  exact (surjStabVec_inj e).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInj_fst_eq

/-- Equal images under `vdkRowPar` have equal stabilized Steinberg parameters. -/
theorem vdkRowParInj_stab_eq {v v' : Fin n → R} {g g' : St n R}
    (h : vdkRowPar (v, g) = vdkRowPar (v', g')) : stab n R g = stab n R g' := by
  have hv : v = v' := vdkRowParInj_fst_eq h
  rw [vdkRowPar_apply, vdkRowPar_apply, hv] at h
  exact mul_left_cancel h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInj_stab_eq

/-- `ker stab ≤ K₂`: if `stab u = 1`, then `u ∈ K₂(n, R)`. -/
theorem vdkRowParInj_mem_K2_of_stab_eq_one {u : St n R} (hu : stab n R u = 1) :
    u ∈ K2n n R := by
  refine (mem_K2_iff u).mpr ?_
  have hinj : Function.Injective (elementaryStab n R) :=
    GroupApproximation.ElementaryPadding.elementaryPad_injective (R := R) Fin.castSuccEmb
  apply hinj
  rw [← projection_stab, hu]
  simp only [map_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInj_mem_K2_of_stab_eq_one

/-- If `K₂(n, R) → K₂(n+1, R)` is injective, then so is `stab : St_n(R) → St_{n+1}(R)`. -/
theorem vdkRowParInj_eq_of_stab_eq (hK : Function.Injective (K2Stab n R)) {g g' : St n R}
    (h : stab n R g = stab n R g') : g = g' := by
  have hu : stab n R (g * g'⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hmem : g * g'⁻¹ ∈ K2n n R := vdkRowParInj_mem_K2_of_stab_eq_one hu
  have hK1 : K2Stab n R ⟨g * g'⁻¹, hmem⟩ = 1 :=
    Subtype.ext (by rw [K2Stab_apply]; exact hu)
  have h1 : (⟨g * g'⁻¹, hmem⟩ : K2n n R) = 1 :=
    hK (hK1.trans (map_one (K2Stab n R)).symm)
  have h2 : g * g'⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.mp h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInj_eq_of_stab_eq

/-- **Over any ring**, injectivity of `K₂(n, R) → K₂(n+1, R)` gives injectivity of the
parabolic map `vdkRowPar : R^n × St_n(R) → St_{n+1}(R)`. -/
theorem vdkRowParInjective_of_K2Stab_injective (hK : Function.Injective (K2Stab n R)) :
    Function.Injective (vdkRowPar (n := n) (R := R)) := by
  rintro ⟨v, g⟩ ⟨v', g'⟩ h
  have hv : v = v' := vdkRowParInj_fst_eq h
  have hg : g = g' := vdkRowParInj_eq_of_stab_eq hK (vdkRowParInj_stab_eq h)
  rw [hv, hg]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInjective_of_K2Stab_injective

end GroupApproximation.BooneHigman.Metabelian.ElemFP
