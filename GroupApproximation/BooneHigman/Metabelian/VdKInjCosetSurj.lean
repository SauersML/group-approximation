import GroupApproximation.BooneHigman.Metabelian.VdKInjCosetStab
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowParInjReadout
import GroupApproximation.Meta.AxiomGuard

/-!
# Step A: the row stabiliser equals the parabolic image

Lane `bh-met-91j`, second file.  `P = vdkRowParSubgroup n R` is the image of
`(v, g) ↦ colVec v · stab g`, and `VdKInjCosetStab` proves `P ≤ rowStab`.

* `vdkInjCoset_RowStabAt n R`: the reverse inclusion `rowStab ≤ P` (Step A of the lane).
* `vdkInjCoset_K2_le_map_of_rowStabAt`: Step A gives `K₂(n+1, R) ≤ stab(K₂(n, R))`.
  For `y ∈ K₂(n+1)`, Step A writes `y = colVec v · stab g`.  The matrix of `y` is `1`, and it
  sends `(0, 1)` to `(v, 1)`, so `v = 0`.  Then `y = stab g`, and `g ∈ K₂(n)` because the
  identity padding `E_n → E_{n+1}` is injective.
* `vdkInjCoset_K2Stab_surjective_of_rowStabAt`: the same fact as surjectivity of `K2Stab n R`.
* `vdkInjCoset_ElemRowStabAt n R`: the elementary-matrix shadow of Step A.  Every `g` fixing
  `e_last` has the matrix of some element of `P`.
* `vdkInjCoset_rowStabAt_iff`: Step A holds iff surjective `K₂` stability and the elementary
  shadow both hold.  The converse direction needs no centrality.

LOUD (truth check).  Step A is a **surjective-type** statement.  By the `iff`, it is equivalent to
`K₂(n+1) ≤ stab K₂(n)` together with an `E`-level statement.  That `E`-level statement says
`GL_n(R) ∩ E_{n+1}(R) = E_n(R)` on the block-diagonal part, i.e. the `K₁`-level injective
stability.  Both are TRUE for `n ≥ sr(R) + 1` (van der Kallen's `K₂` surjective stability;
Bass–Vaserstein `K₁` injective stability).  But Step A does **not** imply injectivity of
`K2Stab`: it says nothing about the kernel of `K₂(n) → K₂(n+1)`.  So the lane's Step B
("deduce injectivity from Step A") is not a valid deduction.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 (colVec colVec_zero)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
  (padMat padMat_of_mem_K2)
open GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero (surjStabVec_inj)
open scoped Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

variable (n R) in
/-- **Step A** at level `n`: every `g ∈ St_{n+1}(R)` fixing the row `e_last` lies in the parabolic
image `P = {colVec v · stab h}`. -/
def vdkInjCoset_RowStabAt : Prop :=
  vdkInjCoset_rowStab n R ≤ vdkRowParSubgroup n R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_RowStabAt

/-- If `stab g ∈ K₂(n+1, R)`, then `g ∈ K₂(n, R)`. -/
theorem vdkInjCoset_mem_K2_of_stab_mem {g : St n R} (hg : stab n R g ∈ K2n (n + 1) R) :
    g ∈ K2n n R := by
  refine (mem_K2_iff g).mpr ?_
  have hinj : Function.Injective (elementaryStab n R) :=
    GroupApproximation.ElementaryPadding.elementaryPad_injective (R := R) Fin.castSuccEmb
  apply hinj
  rw [← projection_stab, (mem_K2_iff _).mp hg]
  simp only [map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_mem_K2_of_stab_mem

/-- **Step A ⟹ surjective `K₂` stability** (as subgroups): `K₂(n+1, R) ≤ stab(K₂(n, R))`. -/
theorem vdkInjCoset_K2_le_map_of_rowStabAt (h : vdkInjCoset_RowStabAt n R) :
    K2n (n + 1) R ≤ (K2n n R).map (stab n R) := by
  intro y hy
  obtain ⟨⟨v, g⟩, hp⟩ := (mem_vdkRowParSubgroup y).mp (h (vdkInjCoset_K2_le_rowStab hy))
  have hv := vdkRowParInj_padMat_mulVec v g
  rw [hp, padMat_of_mem_K2 hy, Matrix.one_mulVec] at hv
  have hv0 : v = 0 := (surjStabVec_inj hv).symm
  subst hv0
  have hy' : stab n R g = y := by
    rw [← hp, vdkRowPar_apply, colVec_zero, one_mul]
  refine Subgroup.mem_map.mpr ⟨g, vdkInjCoset_mem_K2_of_stab_mem ?_, hy'⟩
  rw [hy']
  exact hy

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_K2_le_map_of_rowStabAt

/-- **Step A ⟹ `K2Stab n R` is surjective.** -/
theorem vdkInjCoset_K2Stab_surjective_of_rowStabAt (h : vdkInjCoset_RowStabAt n R) :
    Function.Surjective (K2Stab n R) := by
  rintro ⟨y, hy⟩
  obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp (vdkInjCoset_K2_le_map_of_rowStabAt h hy)
  exact ⟨⟨g, hg⟩, Subtype.ext (by rw [K2Stab_apply]; exact hgy)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_K2Stab_surjective_of_rowStabAt

variable (n R) in
/-- The elementary-matrix shadow of Step A: every `g` fixing `e_last` has the same image in
`E_{n+1}(R)` as some element of the parabolic image `P`. -/
def vdkInjCoset_ElemRowStabAt : Prop :=
  ∀ g ∈ vdkInjCoset_rowStab n R, ∃ p : (Fin n → R) × St n R,
    projection (vdkRowPar p) = projection g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_ElemRowStabAt

/-- **Step A splits** into surjective `K₂` stability and its elementary-matrix shadow. -/
theorem vdkInjCoset_rowStabAt_iff :
    vdkInjCoset_RowStabAt n R ↔
      K2n (n + 1) R ≤ (K2n n R).map (stab n R) ∧ vdkInjCoset_ElemRowStabAt n R := by
  constructor
  · intro h
    refine ⟨vdkInjCoset_K2_le_map_of_rowStabAt h, fun g hg => ?_⟩
    obtain ⟨p, hp⟩ := (mem_vdkRowParSubgroup g).mp (h hg)
    exact ⟨p, by rw [hp]⟩
  · rintro ⟨hK, hE⟩ g hg
    obtain ⟨⟨v, g₀⟩, hp⟩ := hE g hg
    have hk : (vdkRowPar (v, g₀))⁻¹ * g ∈ K2n (n + 1) R := by
      rw [mem_K2_iff, map_mul, map_inv, hp, inv_mul_cancel]
    obtain ⟨k, -, hk'⟩ := Subgroup.mem_map.mp (hK hk)
    have hg' : g = vdkRowPar (v, g₀) * vdkRowPar ((0 : Fin n → R), k) := by
      rw [vdkRowPar_apply (0 : Fin n → R) k, colVec_zero, one_mul, hk', mul_inv_cancel_left]
    rw [hg']
    exact mul_mem ((mem_vdkRowParSubgroup _).mpr ⟨_, rfl⟩)
      ((mem_vdkRowParSubgroup _).mpr ⟨_, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowStabAt_iff

end GroupApproximation.BooneHigman.Metabelian.ElemFP
