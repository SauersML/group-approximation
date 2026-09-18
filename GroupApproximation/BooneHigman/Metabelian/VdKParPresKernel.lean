import GroupApproximation.BooneHigman.Metabelian.VdKParPresTilde
import GroupApproximation.Meta.AxiomGuard

/-!
# The parabolic presentation, part 2: hidden relations and the explicit retraction

Lane `bh-met-92g`.  All of this holds for every commutative `R` and every `n`, unconditionally.

* `vdkParPres_Pi_eq_one_iff`: `Π (v, g) = 1 ↔ v = 0 ∧ stab g = 1`.  This is the matrix readout
  of the last column.
* `vdkParPres_ker_eq`: **the hidden relations**.  `ker Π = inr (ker stab_n)`, and
  `ker stab_n ≤ K₂(n, R)`.  They are the relations among the parabolic generators that hold in
  `St_{n+1}(R)` but not in `R^n ⋊ St_n(R)`.
* `vdkParPres_NoHiddenRel n R := ker Π = ⊥`: "`P` has the presentation `R^n ⋊ St_n(R)`".
* `vdkParPres_parEquiv`: given `NoHiddenRel`, `P ≃* R^n ⋊ St_n(R)`.
* `vdkParPres_retract`: the explicit `φ` on `P`.  It is the projection `rightHom` on the
  presentation: `φ (stab g) = g` and `φ (x_{i,last}(a)) = 1`.  The defining relations of the
  presentation are respected automatically, since `rightHom` is a homomorphism of the
  semidirect product.
* `vdkParPres_parRetract_iff_noHiddenRel`: `ParRetractAt n R ↔ NoHiddenRel n R`.
* `vdkParPres_noHiddenRel_iff_K2Stab_injective`: **LOUD.**  `NoHiddenRel n R` is
  *equivalent* to injectivity of `K2Stab n R`, for every `R` and `n`.  It is not strictly weaker.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 (colVec colVec_zero)

variable {n : ℕ} {R : Type*} [CommRing R]

/-- `Π y = 1` iff the column part is trivial and `stab` kills the Steinberg part. -/
theorem vdkParPres_Pi_eq_one_iff (y : vdkParPres_Tilde n R) :
    vdkParPres_Pi y = 1 ↔ y.left = 1 ∧ stab n R y.right = 1 := by
  rw [vdkParPres_Pi_apply]
  constructor
  · intro h
    have h1 : vdkRowPar (y.left.toAdd, y.right) = vdkRowPar ((0 : Fin n → R), (1 : St n R)) :=
      h.trans vdkRowPar_one.symm
    refine ⟨?_, (vdkRowParInj_stab_eq h1).trans (map_one (stab n R))⟩
    exact Multiplicative.toAdd.injective ((vdkRowParInj_fst_eq h1).trans toAdd_one.symm)
  · rintro ⟨hl, hs⟩
    rw [vdkRowPar_apply, hl, toAdd_one, colVec_zero, one_mul, hs]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_Pi_eq_one_iff

/-- **The hidden relations**: `ker Π = inr (ker stab_n)`. -/
theorem vdkParPres_ker_eq :
    (vdkParPres_Pi (n := n) (R := R)).ker = (stab n R).ker.map vdkParPres_inr := by
  refine Subgroup.ext fun y ↦ ?_
  rw [MonoidHom.mem_ker, vdkParPres_Pi_eq_one_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨hl, hs⟩
    exact ⟨y.right, MonoidHom.mem_ker.mpr hs, SemidirectProduct.ext hl.symm rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨rfl, MonoidHom.mem_ker.mp hg⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_ker_eq

variable (n R) in
/-- **No hidden relations in the parabolic**: `Π : R^n ⋊ St_n(R) → P` has trivial kernel.
Equivalently, `P` has the presentation `R^n ⋊ St_n(R)` on the generators `stab x_{ij}(a)`
and `x_{i,last}(a)`. -/
def vdkParPres_NoHiddenRel : Prop :=
  (vdkParPres_Pi (n := n) (R := R)).ker = ⊥

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_NoHiddenRel

theorem vdkParPres_noHiddenRel_iff_injective_Pi :
    vdkParPres_NoHiddenRel n R ↔ Function.Injective (vdkParPres_Pi (n := n) (R := R)) :=
  MonoidHom.ker_eq_bot_iff _

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_noHiddenRel_iff_injective_Pi

theorem vdkParPres_noHiddenRel_iff_stab_injective :
    vdkParPres_NoHiddenRel n R ↔ Function.Injective (stab n R) := by
  rw [vdkParPres_noHiddenRel_iff_injective_Pi]
  constructor
  · intro h
    refine (injective_iff_map_eq_one (stab n R)).mpr fun g hg ↦ ?_
    have h1 : vdkParPres_Pi (vdkParPres_inr g) = 1 := (vdkParPres_Pi_inr g).trans hg
    have h2 := congrArg SemidirectProduct.right
      ((injective_iff_map_eq_one vdkParPres_Pi).mp h _ h1)
    exact h2
  · intro h
    refine (injective_iff_map_eq_one vdkParPres_Pi).mpr fun y hy ↦ ?_
    obtain ⟨hl, hs⟩ := (vdkParPres_Pi_eq_one_iff y).mp hy
    exact SemidirectProduct.ext hl ((injective_iff_map_eq_one (stab n R)).mp h _ hs)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_noHiddenRel_iff_stab_injective

/-- **LOUD (strength).**  No hidden relations is *equivalent* to `K2Stab` injectivity. -/
theorem vdkParPres_noHiddenRel_iff_K2Stab_injective :
    vdkParPres_NoHiddenRel n R ↔ Function.Injective (K2Stab n R) := by
  rw [vdkParPres_noHiddenRel_iff_stab_injective]
  refine ⟨fun hst a b h ↦ Subtype.ext (hst ?_),
    fun hK g g' h ↦ vdkRowParInj_eq_of_stab_eq hK h⟩
  have h2 := congrArg Subtype.val h
  rwa [K2Stab_apply, K2Stab_apply] at h2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_noHiddenRel_iff_K2Stab_injective

/-- Given no hidden relations, `R^n ⋊ St_n(R) ≃* P`. -/
noncomputable def vdkParPres_parEquiv (h : vdkParPres_NoHiddenRel n R) :
    vdkParPres_Tilde n R ≃* vdkRowParSubgroup n R :=
  (MonoidHom.ofInjective (vdkParPres_noHiddenRel_iff_injective_Pi.mp h)).trans
    (MulEquiv.subgroupCongr vdkParPres_range)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_parEquiv

theorem vdkParPres_parEquiv_apply (h : vdkParPres_NoHiddenRel n R) (y : vdkParPres_Tilde n R) :
    (vdkParPres_parEquiv h y : St (n + 1) R) = vdkParPres_Pi y :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_parEquiv_apply

/-- **The explicit retraction** `φ : P →* St_n(R)`.  Read an element of `P` in the presentation
`R^n ⋊ St_n(R)` and project to `St_n(R)`.  On generators, `φ (stab g) = g` and
`φ (x_{i,last}(a)) = 1`. -/
noncomputable def vdkParPres_retract (h : vdkParPres_NoHiddenRel n R) :
    vdkRowParSubgroup n R →* St n R :=
  SemidirectProduct.rightHom.comp (vdkParPres_parEquiv h).symm.toMonoidHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_retract

theorem vdkParPres_parEquiv_symm_stab (h : vdkParPres_NoHiddenRel n R) (g : St n R) :
    (vdkParPres_parEquiv h).symm ⟨stab n R g, vdkInjCocycle_stab_mem_par g⟩ =
      vdkParPres_inr g := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext ((vdkParPres_parEquiv_apply h _).trans (vdkParPres_Pi_inr g)).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_parEquiv_symm_stab

/-- `φ (stab g) = g`. -/
theorem vdkParPres_retract_stab (h : vdkParPres_NoHiddenRel n R) (g : St n R) :
    vdkParPres_retract h ⟨stab n R g, vdkInjCocycle_stab_mem_par g⟩ = g := by
  change SemidirectProduct.rightHom
    ((vdkParPres_parEquiv h).symm ⟨stab n R g, vdkInjCocycle_stab_mem_par g⟩) = g
  rw [vdkParPres_parEquiv_symm_stab h g]
  exact SemidirectProduct.rightHom_inr g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_retract_stab

theorem vdkParPres_parEquiv_symm_col (h : vdkParPres_NoHiddenRel n R) (v : Fin n → R)
    (hv : colVec v ∈ vdkRowParSubgroup n R) :
    (vdkParPres_parEquiv h).symm ⟨colVec v, hv⟩ =
      SemidirectProduct.inl (Multiplicative.ofAdd v) := by
  rw [MulEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  change colVec v = colVec v * stab n R 1
  rw [map_one, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_parEquiv_symm_col

/-- `φ (x(v)) = 1` for every last-column element `x(v) = ∏ᵢ x_{i,last}(vᵢ)`. -/
theorem vdkParPres_retract_col (h : vdkParPres_NoHiddenRel n R) (v : Fin n → R)
    (hv : colVec v ∈ vdkRowParSubgroup n R) :
    vdkParPres_retract h ⟨colVec v, hv⟩ = 1 := by
  change SemidirectProduct.rightHom ((vdkParPres_parEquiv h).symm ⟨colVec v, hv⟩) = 1
  rw [vdkParPres_parEquiv_symm_col h v hv]
  exact SemidirectProduct.rightHom_inl _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_retract_col

/-- No hidden relations gives the parabolic retraction, with the explicit `φ`. -/
theorem vdkParPres_parRetract_of_noHiddenRel (h : vdkParPres_NoHiddenRel n R) :
    vdkInjCocycle_ParRetractAt n R :=
  ⟨vdkParPres_retract h, vdkParPres_retract_stab h⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_parRetract_of_noHiddenRel

theorem vdkParPres_noHiddenRel_of_parRetract (h : vdkInjCocycle_ParRetractAt n R) :
    vdkParPres_NoHiddenRel n R :=
  vdkParPres_noHiddenRel_iff_stab_injective.mpr (vdkInjCocycle_stab_injective_of_parRetract h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_noHiddenRel_of_parRetract

/-- **LOUD.**  The parabolic retraction is *equivalent* to no hidden relations. -/
theorem vdkParPres_parRetract_iff_noHiddenRel :
    vdkInjCocycle_ParRetractAt n R ↔ vdkParPres_NoHiddenRel n R :=
  ⟨vdkParPres_noHiddenRel_of_parRetract, vdkParPres_parRetract_of_noHiddenRel⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_parRetract_iff_noHiddenRel

end GroupApproximation.BooneHigman.Metabelian.ElemFP
