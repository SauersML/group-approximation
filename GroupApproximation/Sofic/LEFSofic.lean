import GroupApproximation.Sofic.Sofic
import GroupApproximation.Sofic.LEF
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.GroupTheory.SemidirectProduct

/-!
# LEF groups are sofic, and residually finite groups are LEF

The two positive inclusions of the approximation hierarchy, in the form this
library states them.

**LEF ⇒ sofic.**  A local embedding of a finite test set into a finite group
is *exactly* multiplicative and *exactly* injective, so the left-regular
representation of the target turns it into a permutation model of the best
possible quality: multiplicative defect `0`, and Hamming separation `1` —
left translations by distinct elements disagree everywhere.  The
quantifier-free heart of the argument is that the sofic definition asks for
approximations that local embeddings deliver exactly.

**Residually finite ⇒ LEF.**  A finite test set has finitely many nonidentity
difference quotients; a finite-index normal subgroup avoiding all of them
makes the quotient map injective on the set, and a quotient map is globally
multiplicative.  The finite quotient then acts on itself, giving the
permutation target the `IsLEF` definition asks for.

Together with `isSofic_of_finite`, these place the classical inclusions

  finite ⊆ residually finite ⊆ LEF ⊆ sofic

in the library.  The classical input for the quotient-nonclosure theorem —
residual finiteness of free groups — is `Sofic/FreeGroupResiduallyFinite`,
and the theorem itself is `Endpoint/QuotientNonclosure`.
-/

namespace GroupApproximation

variable {G : Type*} [Group G]

/-! ### Left-regular permutation models -/

section LeftRegular

variable {Q : Type*} [Group Q]

/-- Left translation, as a permutation of the finite group. -/
def leftRegular (q : Q) : Equiv.Perm Q := Equiv.mulLeft q

@[simp] theorem leftRegular_apply (q x : Q) : leftRegular q x = q * x := rfl

theorem leftRegular_mul (q r : Q) :
    leftRegular (q * r) = leftRegular q * leftRegular r := by
  ext x
  simp [leftRegular]

/-- Left translations by distinct elements disagree at every point. -/
theorem leftRegular_disagreement_univ [Fintype Q] [DecidableEq Q]
    {q r : Q} (hqr : q ≠ r) :
    hammingDisagreement (leftRegular q) (leftRegular r) = Finset.univ := by
  ext x
  simp only [mem_hammingDisagreement, Finset.mem_univ, iff_true,
    leftRegular_apply]
  intro h
  exact hqr (mul_right_cancel h)

/-- The model carrier of a `FiniteModel` lives in `Type`, so this one is
stated there rather than for the ambient universe-polymorphic `Q`; it is only
ever applied to a permutation group of a `Fin n`. -/
theorem hammingDistance_leftRegular {Y : Type} [Group Y] [Fintype Y]
    [DecidableEq Y] {q r : Y} (hqr : q ≠ r) :
    hammingDistance ⟨Y, inferInstance, inferInstance⟩
      (leftRegular q) (leftRegular r) = 1 := by
  have hcard : (0 : ℝ) < Fintype.card Y := by
    exact_mod_cast Fintype.card_pos
  rw [hammingDistance, leftRegular_disagreement_univ hqr,
    Finset.card_univ, div_self (ne_of_gt hcard)]

end LeftRegular

/-! ### LEF implies sofic -/

/-- **LEF groups are sofic.**  The models produced are exact: multiplicative
defect zero and separation one, uniformly in the requested tolerance. -/
theorem isSofic_of_isLEF (h : IsLEF G) : IsSofic G := by
  classical
  intro F ε hε
  obtain ⟨n, f, hinj, hmul⟩ := h F
  refine ⟨{
    carrier := ⟨Equiv.Perm (Fin n), inferInstance, inferInstance⟩
    nonempty := Fintype.card_pos
    map := fun g => leftRegular (f g)
    multiplicative := by
      intro g hg k hk
      have hf : f (g * k) = f g * f k := hmul.map_mul g hg k hk
      rw [hf, leftRegular_mul, hammingDistance_self]
      exact le_of_lt hε
    separated := by
      intro g hg k hk hgk
      have hfk : f g ≠ f k := fun hcon => hgk (hinj hg hk hcon)
      rw [hammingDistance_leftRegular hfk]
      linarith only [hε] }⟩

/-! ### Residually finite implies LEF -/

/-- The permutation form of a finite group: its left-regular image inside the
permutations of an enumeration of its elements. -/
noncomputable def finitePermForm {Q : Type*} [Group Q] [Fintype Q]
    (q : Q) : Equiv.Perm (Fin (Fintype.card Q)) :=
  ((Fintype.equivFin Q).permCongr (leftRegular q))

theorem finitePermForm_one {Q : Type*} [Group Q] [Fintype Q]
    : finitePermForm (1 : Q) = 1 := by
  ext x
  simp [finitePermForm, Equiv.permCongr_apply, leftRegular]

theorem finitePermForm_mul {Q : Type*} [Group Q] [Fintype Q]
    (q r : Q) :
    finitePermForm (q * r) = finitePermForm q * finitePermForm r := by
  ext x
  simp [finitePermForm, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    leftRegular]

theorem finitePermForm_injective {Q : Type*} [Group Q] [Fintype Q]
    :
    Function.Injective (finitePermForm (Q := Q)) := by
  intro q r hqr
  have h1 := congrArg (fun p => p ((Fintype.equivFin Q) 1)) hqr
  simp only [finitePermForm, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    leftRegular_apply, mul_one] at h1
  exact (Fintype.equivFin Q).injective h1

/-- **Residually finite groups are LEF.**  The local embedding is the
quotient by a finite-index normal subgroup avoiding the finitely many
nonidentity difference quotients of the test set, followed by the
left-regular permutation form of the finite quotient. -/
theorem isLEF_of_residuallyFinite [Group.ResiduallyFinite G] : IsLEF G := by
  classical
  intro s
  -- the nonidentity difference quotients of the test set
  set D : Finset G :=
    ((s ×ˢ s).filter fun p => p.1 ≠ p.2).image fun p => p.1⁻¹ * p.2 with hD
  have hD_ne_one : ∀ d ∈ D, d ≠ 1 := by
    intro d hd
    rw [hD, Finset.mem_image] at hd
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hd
    rw [Finset.mem_filter] at hxy
    intro hcon
    exact hxy.2 (by
      have := congrArg (fun z => x * z) hcon
      simpa [mul_assoc] using this.symm)
  -- a finite-index normal subgroup avoiding each difference
  have hchoice : ∀ d : {x // x ∈ D}, ∃ N : Subgroup G,
      N.Normal ∧ N.FiniteIndex ∧ d.1 ∉ N := by
    intro d
    obtain ⟨H, hnotmem⟩ :=
      Group.exists_finiteIndexNormalSubgroup_notMem d.1 (hD_ne_one d.1 d.2)
    exact ⟨H.toSubgroup, H.isNormal', H.isFiniteIndex', hnotmem⟩
  choose Nd hNd_normal hNd_index hNd_notmem using hchoice
  -- their intersection over the finitely many differences
  set N : Subgroup G := ⨅ d : {x // x ∈ D}, Nd d with hN
  haveI hN_normal : N.Normal := by
    constructor
    intro g hg x
    rw [hN, Subgroup.mem_iInf] at hg ⊢
    intro d
    exact (hNd_normal d).conj_mem g (hg d) x
  haveI : ∀ d : {x // x ∈ D}, (Nd d).FiniteIndex := hNd_index
  haveI hN_index : N.FiniteIndex := by
    rw [hN]
    exact Subgroup.finiteIndex_iInf hNd_index
  -- the finite quotient, with classical instances for the permutation form
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  letI : DecidableEq (G ⧸ N) := Classical.decEq _
  refine ⟨Fintype.card (G ⧸ N),
    fun g => finitePermForm (QuotientGroup.mk' N g), ?_, ?_⟩
  · -- injectivity on the test set: a collapse would put a difference
    -- quotient into `N`, hence into the subgroup chosen to avoid it
    intro x hx y hy hxy
    by_contra hne
    have hmem : x⁻¹ * y ∈ D := by
      rw [hD, Finset.mem_image]
      exact ⟨(x, y), by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hne⟩, rfl⟩
    have hquot : QuotientGroup.mk' N x = QuotientGroup.mk' N y :=
      finitePermForm_injective hxy
    have hinN : x⁻¹ * y ∈ N := by
      rw [← QuotientGroup.ker_mk' N]
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      rw [hquot]
      simp
    have hinNd : x⁻¹ * y ∈ Nd ⟨x⁻¹ * y, hmem⟩ := by
      rw [hN] at hinN
      exact Subgroup.mem_iInf.mp hinN ⟨x⁻¹ * y, hmem⟩
    exact hNd_notmem ⟨x⁻¹ * y, hmem⟩ hinNd
  · -- exact multiplicativity, from the quotient map and the permutation form
    constructor
    · rw [map_one, finitePermForm_one]
    · intro x _ y _
      rw [map_mul, finitePermForm_mul]

/-- **Residual finiteness pulls back along injective homomorphisms**: a
group that embeds in a residually finite group is residually finite. -/
theorem residuallyFinite_of_injective {G' : Type*} [Group G']
    (f : G →* G') (hf : Function.Injective f)
    [Group.ResiduallyFinite G'] :
    Group.ResiduallyFinite G := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  have hfg : f g ≠ 1 := fun h ↦ hg (hf (by simpa using h))
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem (f g) hfg
  letI := N.isNormal'
  letI := N.isFiniteIndex'
  refine ⟨G' ⧸ N.toSubgroup, inferInstance, inferInstance,
    (QuotientGroup.mk' N.toSubgroup).comp f, fun hcon ↦ hN ?_⟩
  have hmk : QuotientGroup.mk' N.toSubgroup (f g) = 1 := by
    simpa using hcon
  exact (QuotientGroup.eq_one_iff (f g)).mp (by simpa using hmk)

/-- **Residual finiteness passes to finite-index overgroups**: a group with
a residually finite subgroup of finite index is residually finite.  In
particular, with `FreeGroupResiduallyFinite`, virtually free groups are
residually finite. -/
theorem residuallyFinite_of_finiteIndex
    (H : Subgroup G) [H.FiniteIndex] [Group.ResiduallyFinite H] :
    Group.ResiduallyFinite G := by
  rw [Group.residuallyFinite_iff_exists_finiteIndex]
  intro g hg
  by_cases hgH : g ∈ H
  · have hne : (⟨g, hgH⟩ : H) ≠ 1 := by
      intro hcon
      exact hg (congrArg Subtype.val hcon)
    obtain ⟨K, hKfi, hKnot⟩ :=
      (Group.residuallyFinite_iff_exists_finiteIndex (G := H)).mp
        inferInstance ⟨g, hgH⟩ hne
    refine ⟨K.map H.subtype, ⟨?_⟩, ?_⟩
    · rw [Subgroup.index_map_subtype]
      exact Nat.mul_ne_zero hKfi.index_ne_zero
        Subgroup.FiniteIndex.index_ne_zero
    · intro hmem
      obtain ⟨k, hk, hkval⟩ := Subgroup.mem_map.mp hmem
      have hkeq : k = ⟨g, hgH⟩ := Subtype.ext hkval
      exact hKnot (hkeq ▸ hk)
  · exact ⟨H, ‹_›, hgH⟩

/-- **The site-action kernel trick**: a semidirect product `M ⋊[φ] Γ` of
residually finite groups is residually finite whenever the action has
finite range --- for instance, when `Γ` acts by permuting a finite
generating configuration of `M`.  The kernel of the action has finite
index in `Γ`, its preimage in the semidirect product is a direct product
`M × ker φ` of residually finite groups, and residual finiteness passes
to the finite-index overgroup. -/
theorem residuallyFinite_semidirectProduct_of_finite_range
    {M Γ : Type*} [Group M] [Group Γ] (φ : Γ →* MulAut M)
    [Group.ResiduallyFinite M] [Group.ResiduallyFinite Γ]
    [Finite φ.range] :
    Group.ResiduallyFinite (M ⋊[φ] Γ) := by
  classical
  set H : Subgroup (M ⋊[φ] Γ) :=
    Subgroup.comap (SemidirectProduct.rightHom) φ.ker with hHdef
  haveI : H.FiniteIndex := by
    constructor
    rw [hHdef,
      Subgroup.index_comap_of_surjective _ SemidirectProduct.rightHom_surjective,
      Subgroup.index_ker φ]
    exact Nat.card_ne_zero.mpr ⟨⟨⟨1, φ.range.one_mem⟩⟩, ‹_›⟩
  haveI : Group.ResiduallyFinite H := by
    have hker : ∀ x : H, (x : M ⋊[φ] Γ).right ∈ φ.ker := fun x ↦
      Subgroup.mem_comap.mp x.2
    let χ : H →* M × φ.ker :=
      { toFun := fun x ↦ ((x : M ⋊[φ] Γ).left,
          ⟨(x : M ⋊[φ] Γ).right, hker x⟩)
        map_one' := rfl
        map_mul' := by
          intro x y
          refine Prod.ext ?_ (Subtype.ext ?_)
          · show ((x : M ⋊[φ] Γ) * y).left
              = (x : M ⋊[φ] Γ).left * (y : M ⋊[φ] Γ).left
            rw [SemidirectProduct.mul_left,
              MonoidHom.mem_ker.mp (hker x)]
            simp
          · show ((x : M ⋊[φ] Γ) * y).right
              = (x : M ⋊[φ] Γ).right * (y : M ⋊[φ] Γ).right
            exact SemidirectProduct.mul_right _ _ }
    have hχ : Function.Injective χ := by
      intro x y hxy
      have h1 : (x : M ⋊[φ] Γ).left = (y : M ⋊[φ] Γ).left :=
        congrArg Prod.fst hxy
      have h2 : (x : M ⋊[φ] Γ).right = (y : M ⋊[φ] Γ).right :=
        congrArg Subtype.val (congrArg Prod.snd hxy)
      exact Subtype.ext (SemidirectProduct.ext h1 h2)
    exact residuallyFinite_of_injective χ hχ
  exact residuallyFinite_of_finiteIndex H

/-- Residual finiteness transfers along group isomorphisms. -/
theorem residuallyFinite_of_mulEquiv {G' : Type*} [Group G']
    (e : G ≃* G') [Group.ResiduallyFinite G'] :
    Group.ResiduallyFinite G :=
  residuallyFinite_of_injective e.toMonoidHom e.injective

/-- **Exhaustion by residually finite subgroups gives LEF**: if every
finite subset lies in a residually finite subgroup, the group is LEF.
This is the quantifier order the telescope-core argument consumes: the
subgroup may depend on the finite subset arbitrarily. -/
theorem isLEF_of_forall_finset_residuallyFinite
    (h : ∀ s : Finset G, ∃ H : Subgroup G,
      (∀ x ∈ s, x ∈ H) ∧ Group.ResiduallyFinite H) : IsLEF G :=
  isLEF_of_forall_finset_subgroup fun s ↦ by
    obtain ⟨H, hs, hH⟩ := h s
    exact ⟨H, hs, letI := hH; isLEF_of_residuallyFinite⟩

/-- Exhaustion by residually finite subgroups gives soficity. -/
theorem isSofic_of_forall_finset_residuallyFinite
    (h : ∀ s : Finset G, ∃ H : Subgroup G,
      (∀ x ∈ s, x ∈ H) ∧ Group.ResiduallyFinite H) : IsSofic G :=
  isSofic_of_isLEF (isLEF_of_forall_finset_residuallyFinite h)

/-- The cyclic subgroup generated by a central element is normal. -/
theorem normal_zpowers_of_mem_center {z : G}
    (hz : z ∈ Subgroup.center G) :
    (Subgroup.zpowers z).Normal := by
  constructor
  intro a ha g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hc : z ^ k ∈ Subgroup.center G :=
    Subgroup.zpow_mem _ hz k
  have hcm := (Subgroup.mem_center_iff.mp hc) g
  rw [hcm, mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k

end GroupApproximation
