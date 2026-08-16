import GroupApproximation.Sofic.MatricialStabilityRadical
import GroupApproximation.Algebra.FiniteResidual

/-!
# The finite-dimensional residual sits inside the finite residual

**Equation 41.3** of the dossier, second inclusion.  Every finite quotient set
carries a faithful finite-dimensional unitary representation — the permutation
representation on the cosets — so an element invisible to all finite-dimensional
unitary representations already lies in every finite-index subgroup.

Combined with `actualCoronaMFResidual_le_fdUnitaryResidual`, which the
matricial-stability module already supplies, this closes the chain

`Res_MF ≤ Rad_fd ≤ Res_fin`

for every group; in the dossier's concrete family all three coincide.

The transport through `Fin n` is not cosmetic: `FiniteModel` carries a `Type`
(universe `0`) coordinate set, while `G ⧸ L` lives in the universe of `G`.
-/

namespace GroupApproximation

open MatricialStabilityRadical

universe u v w

/-- Transport of permutations along an equivalence of the underlying types, as
a monoid homomorphism. -/
def permCongrHom {α : Type v} {β : Type w} (e : α ≃ β) :
    Equiv.Perm α →* Equiv.Perm β where
  toFun p := (e.symm.trans p).trans e
  map_one' := by ext x; simp
  map_mul' p q := by ext x; simp

@[simp] theorem permCongrHom_apply {α : Type v} {β : Type w} (e : α ≃ β)
    (p : Equiv.Perm α) (x : β) : permCongrHom e p x = e (p (e.symm x)) := rfl

/-- Permutations as unitary matrices.  Taking the matrix of a permutation
reverses products, so the homomorphism inverts first. -/
noncomputable def permUnitaryHom (Y : FiniteModel) :
    Equiv.Perm Y →* Matrix.unitaryGroup Y ℂ where
  toFun σ := ⟨(σ⁻¹).permMatrix ℂ, permMatrix_mem_unitaryGroup Y σ⁻¹⟩
  map_one' := by
    refine Subtype.ext ?_
    show ((1 : Equiv.Perm Y)⁻¹).permMatrix ℂ = (1 : Matrix Y Y ℂ)
    rw [inv_one]
    ext i j
    rw [permMatrixC_entry, Matrix.one_apply]
    simp
  map_mul' := fun σ τ => by
    refine Subtype.ext ?_
    show ((σ * τ)⁻¹).permMatrix ℂ
      = ((σ⁻¹).permMatrix ℂ) * ((τ⁻¹).permMatrix ℂ)
    rw [_root_.mul_inv_rev, Matrix.permMatrix_mul]

/-- The permutation representation is faithful: only the identity permutation
has the identity matrix. -/
theorem perm_eq_one_of_permMatrix_eq_one {Y : FiniteModel} {σ : Equiv.Perm Y}
    (h : (σ).permMatrix ℂ = (1 : Matrix Y Y ℂ)) : σ = 1 := by
  classical
  refine Equiv.ext fun i => ?_
  have hij : (σ.permMatrix ℂ) i (σ i) = (1 : Matrix Y Y ℂ) i (σ i) := by rw [h]
  rw [permMatrixC_entry, if_pos rfl, Matrix.one_apply] at hij
  by_cases hcase : i = σ i
  · exact hcase.symm
  · rw [if_neg hcase] at hij
    exact absurd hij one_ne_zero

theorem permUnitaryHom_injective (Y : FiniteModel) :
    Function.Injective (permUnitaryHom Y) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hval : ((σ⁻¹).permMatrix ℂ) = (1 : Matrix Y Y ℂ) :=
    congrArg Subtype.val hσ
  have : σ⁻¹ = 1 := perm_eq_one_of_permMatrix_eq_one hval
  simpa using congrArg (fun p : Equiv.Perm Y => p⁻¹) this

variable {G : Type u} [Group G]

/-- **Equation 41.3, second inclusion.**  An element invisible to every
finite-dimensional unitary representation lies in every finite-index
subgroup. -/
theorem fdUnitaryResidual_le_finiteResidual :
    fdUnitaryResidual G ≤ finiteResidual G := by
  classical
  intro x hx
  rw [mem_finiteResidual_iff]
  intro L hL
  haveI := hL
  haveI : Fintype (G ⧸ L) := Fintype.ofFinite _
  set n : ℕ := Fintype.card (G ⧸ L) with hn
  set e : (G ⧸ L) ≃ Fin n := Fintype.equivFin _ with he
  set Y : FiniteModel := ⟨Fin n, inferInstance, inferInstance⟩ with hY
  -- the coset permutation representation, transported to `Fin n`
  set σ : G →* Equiv.Perm (Fin n) :=
    (permCongrHom e).comp (MulAction.toPermHom G (G ⧸ L)) with hσ
  have hphi := (mem_fdUnitaryResidual_iff).mp hx Y ((permUnitaryHom Y).comp σ)
  have hone : σ x = 1 := permUnitaryHom_injective Y (by simpa using hphi)
  -- the trivial permutation means `x` fixes the base coset
  have happ := congrArg (fun p : Equiv.Perm (Fin n) =>
    p (e (QuotientGroup.mk (1 : G) : G ⧸ L))) hone
  simp only [hσ, MonoidHom.coe_comp, Function.comp_apply, permCongrHom_apply,
    Equiv.symm_apply_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    Equiv.Perm.coe_one, id_eq] at happ
  have hfix : (x : G) • (QuotientGroup.mk 1 : G ⧸ L) = QuotientGroup.mk 1 :=
    e.injective happ
  have hq : (QuotientGroup.mk x : G ⧸ L) = QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at hfix
    exact hfix
  have hmem : x⁻¹ ∈ L := by simpa using (QuotientGroup.eq (s := L)).mp hq
  simpa using L.inv_mem hmem

/-- The full chain of Equation 41.3: the MF radical is contained in the finite
residual. -/
theorem actualCoronaMFResidual_le_finiteResidual :
    actualCoronaMFResidual G ≤ finiteResidual G :=
  le_trans actualCoronaMFResidual_le_fdUnitaryResidual
    fdUnitaryResidual_le_finiteResidual

end GroupApproximation
