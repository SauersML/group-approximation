import Mathlib.Data.ZMod.Basic
import GroupApproximation.Algebra.VisibleQuotient
import GroupApproximation.Criterion.FiniteQuotientBlindness
import GroupApproximation.Sofic.AscendingHNNDoubleCosets
import GroupApproximation.Sofic.FiniteDimensionalResidual
import GroupApproximation.Sofic.IntegralLinearResiduallyFinite
import GroupApproximation.Sofic.ProfiniteClosure
import GroupApproximation.Sofic.SoficTelescope

/-!
# Exact profinite closure of the base in an ascending HNN extension

Let `Vertical α hα = Telescope(α) ⋊ ℤ` be the standard ascending-HNN model and
let `B = range (iotaVertical α hα)` be its level-zero base copy.  A finite
quotient cannot see the strict one-sided compression: the image of `B` is
normalized by the stable letter.  Repeated reverse conjugation therefore sends
every telescope level into the image of `B` in every finite quotient.

The converse is detected by the height map to `ℤ`, reduced modulo a finite
cyclic group.  Consequently the profinite closure is identified exactly:

`profiniteClosure B = ker (height α hα)`.

This has two useful consequences.

* Every finite-index subgroup of `Vertical α hα` containing `B` contains the
  entire height-zero telescope kernel.
* The base copy is subgroup-separable in the ascending HNN extension if and
  only if `α` is surjective.  In particular, for every proper injective
  self-embedding the separable-base route to soficity is unavailable, not just
  difficult to verify.

The statements are independent of property `(T)`, residual finiteness, and
soficity of the base.
-/

namespace GroupApproximation
namespace MarkedCompression

open MappingTelescope SemidirectProduct

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The level-zero base subgroup in the ascending-HNN model. -/
abbrev ascendingHNNBase : Subgroup (Vertical α hα) :=
  (iotaVertical α hα).range

/-- The height-zero mapping-telescope kernel. -/
abbrev ascendingHNNHeightKernel : Subgroup (Vertical α hα) :=
  (height α hα).ker

include hα in
/-- The stable letter compresses the level-zero base into itself. -/
private theorem ascendingHNNBase_compressed (v : Vertical α hα)
    (hv : v ∈ ascendingHNNBase α hα) :
    tVertical α hα * v * (tVertical α hα)⁻¹ ∈ ascendingHNNBase α hα := by
  obtain ⟨γ, rfl⟩ := hv
  refine ⟨α γ, ?_⟩
  exact (vertical_compress α hα γ).symm

/-- Inverse conjugation of a base element still has height zero. -/
private theorem height_inv_conj_iota (x : Γ) :
    height α hα ((tVertical α hα)⁻¹ * iotaVertical α hα x * tVertical α hα) = 1 := by
  rw [map_mul, map_mul, map_inv, height_tVertical, height_iotaVertical]
  simp

include hα in
/-- Every telescope level maps into the image of the level-zero base under
any homomorphism to a finite group.  Finite quotients turn one-sided
compression into genuine normalization. -/
theorem finiteQuotient_level_mem_base {Q : Type} [Group Q] [Finite Q]
    (ψ : Vertical α hα →* Q) (n : ℕ) (x : Γ) :
    ψ (inl (level α hα n x) : Vertical α hα) ∈
      (ascendingHNNBase α hα).map ψ := by
  induction n with
  | zero =>
      change ψ (iotaVertical α hα x) ∈ (ascendingHNNBase α hα).map ψ
      exact Subgroup.mem_map_of_mem ψ ⟨x, rfl⟩
  | succ n ih =>
      rw [show Nat.succ n = n + 1 by omega, inl_level_succ]
      simp only [map_mul, map_inv]
      exact compressorImage_normalizes_inv ψ (ascendingHNNBase α hα)
        (ascendingHNNBase_compressed α hα) _ ih

include hα in
/-- The whole height-zero telescope kernel lies in the profinite closure of the
base. -/
theorem ascendingHNNHeightKernel_le_profiniteClosure :
    ascendingHNNHeightKernel α hα ≤
      profiniteClosure (ascendingHNNBase α hα) := by
  intro v hv Q _ _ ψ
  change v ∈ (rightHom : Vertical α hα →* Multiplicative ℤ).ker at hv
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom] at hv
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨n, x, hx⟩ := exists_level_repr α hα a
  rw [← hx]
  exact finiteQuotient_level_mem_base α hα ψ n x

include hα in
/-- Nonzero height is detected by a finite cyclic quotient, so nothing outside
the telescope kernel belongs to the profinite closure of the base. -/
theorem profiniteClosure_le_ascendingHNNHeightKernel :
    profiniteClosure (ascendingHNNBase α hα) ≤
      ascendingHNNHeightKernel α hα := by
  intro v hv
  rw [MonoidHom.mem_ker]
  by_contra hheight
  set nz : ℤ := Multiplicative.toAdd (height α hα v) with hnz
  have hnz0 : nz ≠ 0 := by
    intro hzero
    apply hheight
    have hrew : height α hα v = Multiplicative.ofAdd nz := rfl
    rw [hrew, hzero]
    rfl
  haveI : NeZero (nz.natAbs + 1) := ⟨by omega⟩
  let ψ : Vertical α hα →* Multiplicative (ZMod (nz.natAbs + 1)) :=
    (AddMonoidHom.toMultiplicative
      (Int.castAddHom (ZMod (nz.natAbs + 1)))).comp (height α hα)
  have hmem : ψ v ∈ (ascendingHNNBase α hα).map ψ := hv _ ψ
  obtain ⟨b, hb, hbv⟩ := hmem
  obtain ⟨γ, rfl⟩ := hb
  have hbase : ψ (iotaVertical α hα γ) = 1 := by
    simp [ψ, height_iotaVertical]
  have hvone : ψ v = 1 := by
    rw [← hbv, hbase]
  have hcast : (nz : ZMod (nz.natAbs + 1)) = 0 := by
    have h := congrArg Multiplicative.toAdd hvone
    simpa [ψ, hnz] using h
  exact intCast_zmod_natAbs_add_one_ne_zero hnz0 hcast

include hα in
/-- **Exact profinite closure theorem.**  The profinite closure of the base copy
is exactly the height-zero mapping-telescope kernel. -/
theorem profiniteClosure_ascendingHNNBase_eq_heightKernel :
    profiniteClosure (ascendingHNNBase α hα) =
      ascendingHNNHeightKernel α hα :=
  le_antisymm (profiniteClosure_le_ascendingHNNHeightKernel α hα)
    (ascendingHNNHeightKernel_le_profiniteClosure α hα)

/-- A profinite-closure element lies in every finite-index overgroup of the
original subgroup.  The finite coset action is transported to `Fin n`, so the
finite target is universe-zero, exactly as required by `profiniteClosure`. -/
theorem profiniteClosure_le_finiteIndex_overgroup {G : Type*} [Group G]
    (H K : Subgroup G) [K.FiniteIndex] (hHK : H ≤ K) :
    profiniteClosure H ≤ K := by
  classical
  intro g hg
  haveI : Fintype (G ⧸ K) := Fintype.ofFinite _
  set n : ℕ := Fintype.card (G ⧸ K) with hn
  set e : (G ⧸ K) ≃ Fin n := Fintype.equivFin _ with he
  set ψ : G →* Equiv.Perm (Fin n) :=
    (permCongrHom e).comp (MulAction.toPermHom G (G ⧸ K)) with hψ
  have hmem : ψ g ∈ H.map ψ := hg (Equiv.Perm (Fin n)) ψ
  obtain ⟨h, hhH, hhg⟩ := hmem
  have hhK : h ∈ K := hHK hhH
  have hone : ψ (h⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hhg, inv_mul_cancel]
  have happ := congrArg (fun p : Equiv.Perm (Fin n) =>
    p (e (QuotientGroup.mk (1 : G) : G ⧸ K))) hone
  simp only [hψ, MonoidHom.coe_comp, Function.comp_apply, permCongrHom_apply,
    Equiv.symm_apply_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    Equiv.Perm.coe_one, id_eq] at happ
  have hfix : (h⁻¹ * g) • (QuotientGroup.mk 1 : G ⧸ K) = QuotientGroup.mk 1 :=
    e.injective happ
  have hq : (QuotientGroup.mk (h⁻¹ * g) : G ⧸ K) = QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at hfix
    exact hfix
  have hinv : (h⁻¹ * g)⁻¹ ∈ K := by
    simpa using (QuotientGroup.eq (s := K)).mp hq
  have hrest : h⁻¹ * g ∈ K := K.inv_mem hinv
  have hmul : h * (h⁻¹ * g) ∈ K := K.mul_mem hhK hrest
  simpa using hmul

include hα in
/-- Every finite-index subgroup containing the base contains the entire
height-zero telescope kernel. -/
theorem ascendingHNNHeightKernel_le_finiteIndex_overgroup
    (K : Subgroup (Vertical α hα)) [K.FiniteIndex]
    (hbase : ascendingHNNBase α hα ≤ K) :
    ascendingHNNHeightKernel α hα ≤ K :=
  fun _ hv => profiniteClosure_le_finiteIndex_overgroup
    (ascendingHNNBase α hα) K hbase
      (ascendingHNNHeightKernel_le_profiniteClosure α hα hv)

include hα in
/-- If the height-zero kernel is already contained in the base, then the
self-embedding is onto. -/
theorem surjective_of_ascendingHNNHeightKernel_le_base
    (hker : ascendingHNNHeightKernel α hα ≤ ascendingHNNBase α hα) :
    Function.Surjective α := by
  intro x
  by_contra hx
  have hxset : x ∉ Set.range α := fun h => hx h
  have hnot := tVertical_inv_conj_not_mem α hα hxset
  apply hnot
  apply hker
  rw [MonoidHom.mem_ker]
  exact height_inv_conj_iota α hα x

include hα in
/-- If the self-embedding is onto, every telescope level collapses to level
zero, so the height kernel is the base. -/
theorem ascendingHNNHeightKernel_le_base_of_surjective
    (hsurj : Function.Surjective α) :
    ascendingHNNHeightKernel α hα ≤ ascendingHNNBase α hα := by
  intro v hv
  change v ∈ (rightHom : Vertical α hα →* Multiplicative ℤ).ker at hv
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom] at hv
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨n, x, hx⟩ := exists_level_repr α hα a
  rw [← hx]
  have hlevel : ∀ m : ℕ, ∀ y : Γ,
      level α hα m y ∈ (level α hα 0).range := by
    intro m
    induction m with
    | zero =>
        intro y
        exact ⟨y, rfl⟩
    | succ m ih =>
        intro y
        obtain ⟨z, rfl⟩ := hsurj y
        obtain ⟨w, hw⟩ := ih z
        refine ⟨w, ?_⟩
        exact hw.trans (level_succ_apply_hom α hα m z).symm
  obtain ⟨y, hy⟩ := hlevel n x
  refine ⟨y, ?_⟩
  change (inl (level α hα 0 y) : Vertical α hα) =
    inl (level α hα n x)
  exact congrArg inl hy

include hα in
/-- The level-zero base equals the entire height kernel exactly in the
automorphic case. -/
theorem ascendingHNNBase_eq_heightKernel_iff_surjective :
    ascendingHNNBase α hα = ascendingHNNHeightKernel α hα ↔
      Function.Surjective α := by
  constructor
  · intro h
    apply surjective_of_ascendingHNNHeightKernel_le_base α hα
    intro v hv
    rwa [h]
  · intro hsurj
    apply le_antisymm
    · intro v hv
      rw [MonoidHom.mem_ker]
      exact height_eq_one_of_mem_range α hα hv
    · exact ascendingHNNHeightKernel_le_base_of_surjective α hα hsurj

/-- The finite-index-overgroup formulation of subgroup separability used by the
sofic-action files. -/
def AscendingHNNBaseSeparable : Prop :=
  ∀ g : Vertical α hα, g ∉ ascendingHNNBase α hα →
    ∃ K : Subgroup (Vertical α hα),
      ascendingHNNBase α hα ≤ K ∧ K.FiniteIndex ∧ g ∉ K

include hα in
/-- A single element outside the range witnesses failure of separability of the
base in a proper ascending HNN extension. -/
theorem not_ascendingHNNBaseSeparable_of_not_mem_range
    {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    ¬ AscendingHNNBaseSeparable α hα := by
  intro hsep
  let g : Vertical α hα :=
    (tVertical α hα)⁻¹ * iotaVertical α hα a₀ * tVertical α hα
  have hgnot : g ∉ ascendingHNNBase α hα := by
    simpa [g] using tVertical_inv_conj_not_mem α hα ha₀
  obtain ⟨K, hbase, hKfi, hgK⟩ := hsep g hgnot
  haveI : K.FiniteIndex := hKfi
  apply hgK
  apply ascendingHNNHeightKernel_le_finiteIndex_overgroup α hα K hbase
  rw [MonoidHom.mem_ker]
  simpa [g] using height_inv_conj_iota α hα a₀

include hα in
/-- Every proper injective self-embedding gives a non-separable base copy. -/
theorem not_ascendingHNNBaseSeparable_of_not_surjective
    (hproper : ¬ Function.Surjective α) :
    ¬ AscendingHNNBaseSeparable α hα := by
  have hex : ∃ a₀ : Γ, a₀ ∉ Set.range α := by
    by_contra hnone
    apply hproper
    intro y
    have hy : y ∈ Set.range α := by
      by_contra hy
      exact hnone ⟨y, hy⟩
    exact hy
  obtain ⟨a₀, ha₀⟩ := hex
  exact not_ascendingHNNBaseSeparable_of_not_mem_range α hα ha₀

include hα in
/-- For a proper self-embedding the base is strictly smaller than its profinite
closure. -/
theorem ascendingHNNBase_lt_profiniteClosure_of_not_surjective
    (hproper : ¬ Function.Surjective α) :
    ascendingHNNBase α hα < profiniteClosure (ascendingHNNBase α hα) := by
  refine lt_of_le_of_ne (le_profiniteClosure (ascendingHNNBase α hα)) ?_
  intro heq
  have hbaseker : ascendingHNNBase α hα = ascendingHNNHeightKernel α hα :=
    heq.trans (profiniteClosure_ascendingHNNBase_eq_heightKernel α hα)
  exact hproper ((ascendingHNNBase_eq_heightKernel_iff_surjective α hα).mp hbaseker)

include hα in
/-- Separability of the base forces the self-embedding to be onto. -/
theorem surjective_of_ascendingHNNBaseSeparable
    (hsep : AscendingHNNBaseSeparable α hα) :
    Function.Surjective α := by
  by_contra hproper
  exact (not_ascendingHNNBaseSeparable_of_not_surjective α hα hproper) hsep

include hα in
/-- In the automorphic case the base equals the height kernel, and finite cyclic
quotients of height separate every element outside it. -/
theorem ascendingHNNBaseSeparable_of_surjective
    (hsurj : Function.Surjective α) :
    AscendingHNNBaseSeparable α hα := by
  intro g hg
  have hbaseKer :=
    (ascendingHNNBase_eq_heightKernel_iff_surjective α hα).2 hsurj
  have hheight : height α hα g ≠ 1 := by
    intro hone
    apply hg
    rw [hbaseKer, MonoidHom.mem_ker]
    exact hone
  set nz : ℤ := Multiplicative.toAdd (height α hα g) with hnz
  have hnz0 : nz ≠ 0 := by
    intro hzero
    apply hheight
    have hrew : height α hα g = Multiplicative.ofAdd nz := rfl
    rw [hrew, hzero]
    rfl
  haveI : NeZero (nz.natAbs + 1) := ⟨by omega⟩
  let ψ : Vertical α hα →* Multiplicative (ZMod (nz.natAbs + 1)) :=
    (AddMonoidHom.toMultiplicative
      (Int.castAddHom (ZMod (nz.natAbs + 1)))).comp (height α hα)
  refine ⟨ψ.ker, ?_, VisibleQuotient.finiteIndex_ker ψ, ?_⟩
  · intro b hb
    rw [MonoidHom.mem_ker]
    obtain ⟨γ, rfl⟩ := hb
    simp [ψ, height_iotaVertical]
  · intro hmem
    have hone : ψ g = 1 := MonoidHom.mem_ker.mp hmem
    have hcast : (nz : ZMod (nz.natAbs + 1)) = 0 := by
      have h := congrArg Multiplicative.toAdd hone
      simpa [ψ, hnz] using h
    exact intCast_zmod_natAbs_add_one_ne_zero hnz0 hcast

include hα in
/-- **Exact separability boundary.**  The base copy is subgroup-separable in
the ascending HNN extension if and only if the self-embedding is onto. -/
theorem ascendingHNNBaseSeparable_iff_surjective :
    AscendingHNNBaseSeparable α hα ↔ Function.Surjective α :=
  ⟨surjective_of_ascendingHNNBaseSeparable α hα,
    ascendingHNNBaseSeparable_of_surjective α hα⟩

end MarkedCompression
end GroupApproximation
