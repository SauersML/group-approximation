import GroupApproximation.Sofic.AscendingHNNFolner
import GroupApproximation.Sofic.AscendingHNNCosetActionSofic
import GroupApproximation.Sofic.SoficActionEmbedding
import GroupApproximation.Sofic.SoficActionChabauty
import GroupApproximation.Sofic.SoficActionCyclicExtension
import GroupApproximation.Sofic.SoficActionLocalModels
import GroupApproximation.Sofic.SoficActionQuotientTransfer

/-!
# Exact iterated-coset criterion for an ascending HNN action

Let `α : Γ → Γ` be injective, let `V` be its ascending-HNN mapping-telescope
model, and let `X = V/Γ` be the level-zero coset space.  The obstruction to
soficity of `V ↷ X` lives entirely in the base: one has the exact criterion

`V ↷ X is sofic ↔ ∀ m, Γ ↷ Γ / α^m(Γ) is sofic`.

The difficult direction is local.  Given finite windows in the telescope and in
`X`, choose one telescope level `R` which contains the tested telescope
elements and also the normal parts of representatives of all tested sites.
Every site then has a normal form

`x = (t⁻ᴿ a tᴿ) tᵏ Γ`, with `m = R + k ≥ 0`.

Under the level-`R` copy of `Γ`, conjugated by `a`, the stabilizer of `x` is
exactly `α^m(Γ)`.  Thus each orbit occurring in the finite site window is
modelled by one of the assumed base coset actions.  The local-orbit gluing
lemma builds a model for that window, the local-subgroup lemma lifts it to the
whole telescope, and the cyclic-extension theorem adjoins the stable letter.

No finite-index, residual-finiteness, property `(T)`, or soficity hypothesis on
`Γ` is used.
-/

namespace GroupApproximation
namespace MarkedCompression

open MappingTelescope SemidirectProduct CyclicStack AscendingHNNFolner

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The tower of base coset actions which exactly controls the ascending-HNN
coset action. -/
def IteratedCosetActionsSofic : Prop :=
  ∀ m : ℕ, IsSoficAction Γ (Γ ⧸ (iterateHom α m).range)

/-- Separability of every iterated self-image in the base group.  This is a
strictly base-level condition; unlike separability of the level-zero base
inside the HNN group, it can hold for a proper self-embedding. -/
def IteratedRangesSeparable : Prop :=
  ∀ (m : ℕ) (g : Γ), g ∉ (iterateHom α m).range →
    ∃ K : Subgroup Γ,
      (iterateHom α m).range ≤ K ∧ K.FiniteIndex ∧ g ∉ K

/-- Separability of every iterated range makes every controlling base coset
action sofic. -/
theorem iteratedCosetActionsSofic_of_iteratedRangesSeparable
    (hsep : IteratedRangesSeparable α) :
    IteratedCosetActionsSofic α := by
  intro m
  exact isSoficAction_quotient_of_separable (iterateHom α m).range (hsep m)

/-- A level-`m` telescope element lies in level zero exactly when its label lies
in the range of `α^m`. -/
theorem level_mem_levelZero_iff_iterate (m : ℕ) (x : Γ) :
    level α hα m x ∈ (level α hα 0).range ↔
      x ∈ (iterateHom α m).range := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [level_apply, level_apply, mk_eq_mk_iff] at hy
    simpa using hy
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [level_apply, level_apply, mk_eq_mk_iff]
    simpa using hy

/-- Vertical form of `level_mem_levelZero_iff_iterate`. -/
theorem inl_level_mem_base_iff_iterate (m : ℕ) (x : Γ) :
    (inl (level α hα m x) : Vertical α hα) ∈ (iotaVertical α hα).range ↔
      x ∈ (iterateHom α m).range := by
  constructor
  · rintro ⟨y, hy⟩
    apply (level_mem_levelZero_iff_iterate α hα m x).mp
    refine ⟨y, ?_⟩
    exact inl_injective hy
  · intro hx
    obtain ⟨y, hy⟩ := (level_mem_levelZero_iff_iterate α hα m x).mpr hx
    refine ⟨y, ?_⟩
    exact congrArg inl hy

/-- Integer powers of the stable letter are the pure-height elements. -/
theorem tVertical_zpow_eq_inr (k : ℤ) :
    (tVertical α hα) ^ k =
      (inr (Multiplicative.ofAdd k) : Vertical α hα) := by
  show ((inr (Multiplicative.ofAdd 1) : Vertical α hα)) ^ k = _
  rw [← map_zpow]
  congr 1
  rw [← ofAdd_zsmul]
  simp

/-- Every vertical element is its telescope component followed by its height. -/
theorem vertical_eq_inl_mul_tVertical_zpow (g : Vertical α hα) :
    g = inl g.left * (tVertical α hα) ^ Multiplicative.toAdd g.right := by
  rw [tVertical_zpow_eq_inr]
  have hright : Multiplicative.ofAdd (Multiplicative.toAdd g.right) = g.right :=
    ofAdd_toAdd _
  rw [hright]
  exact (SemidirectProduct.inl_left_mul_inr_right g).symm

include hα in
/-- Conjugating a level-`R` element by height `k` moves it to level `m = R+k`,
provided that level is nonnegative. -/
theorem tVertical_zpow_inv_conj_level {R m : ℕ} {k : ℤ}
    (hm : (m : ℤ) = (R : ℤ) + k) (x : Γ) :
    ((tVertical α hα) ^ k)⁻¹ * inl (level α hα R x) *
        (tVertical α hα) ^ k =
      (inl (level α hα m x) : Vertical α hα) := by
  rw [inl_level_eq_conj α hα R x, inl_level_eq_conj α hα m x]
  have hpow : (tVertical α hα) ^ (m : ℤ) =
      (tVertical α hα) ^ (R : ℤ) * (tVertical α hα) ^ k := by
    rw [← zpow_add, ← hm]
  rw [hpow, mul_inv_rev]
  group

include hα in
/-- The stabilizer computation in the normal form used by the local proof.
The level-`R` copy is parametrized by the conjugated embedding
`γ ↦ level_R(a γ a⁻¹)`. -/
theorem conjugated_level_smul_site_iff {R m : ℕ} {k : ℤ}
    (hm : (m : ℤ) = (R : ℤ) + k) (a γ : Γ) :
    (inl (level α hα R (a * γ * a⁻¹)) : Vertical α hα) •
        ((inl (level α hα R a) * (tVertical α hα) ^ k) • rootCoset α hα)
      = ((inl (level α hα R a) * (tVertical α hα) ^ k) • rootCoset α hα)
      ↔ γ ∈ (iterateHom α m).range := by
  let g : Vertical α hα :=
    inl (level α hα R a) * (tVertical α hα) ^ k
  let z : Vertical α hα :=
    inl (level α hα R (a * γ * a⁻¹))
  have hinner :
      (inl (level α hα R a) : Vertical α hα)⁻¹ * z *
          inl (level α hα R a)
        = inl (level α hα R γ) := by
    let jR : Γ →* Vertical α hα :=
      (inl : Telescope α hα →* Vertical α hα).comp (level α hα R)
    change (jR a)⁻¹ * jR (a * γ * a⁻¹) * jR a = jR γ
    calc
      (jR a)⁻¹ * jR (a * γ * a⁻¹) * jR a =
          jR (a⁻¹ * (a * γ * a⁻¹) * a) := by
            simp only [map_mul, map_inv]
      _ = jR γ := by
        congr 1
        group
  have hconj : g⁻¹ * z * g = inl (level α hα m γ) := by
    calc
      g⁻¹ * z * g =
          ((tVertical α hα) ^ k)⁻¹ *
            ((inl (level α hα R a) : Vertical α hα)⁻¹ * z *
              inl (level α hα R a)) *
            (tVertical α hα) ^ k := by
              simp only [g, mul_inv_rev]
              group
      _ = ((tVertical α hα) ^ k)⁻¹ * inl (level α hα R γ) *
            (tVertical α hα) ^ k := by rw [hinner]
      _ = inl (level α hα m γ) :=
        tVertical_zpow_inv_conj_level α hα hm γ
  change z • (g • rootCoset α hα) = g • rootCoset α hα ↔ _
  rw [← mul_smul, smul_rootCoset, smul_rootCoset, QuotientGroup.eq]
  constructor
  · intro hq
    have hinv := (iotaVertical α hα).range.inv_mem hq
    have hmem : g⁻¹ * z * g ∈ (iotaVertical α hα).range := by
      simpa [mul_inv_rev, mul_assoc] using hinv
    rw [hconj] at hmem
    exact (inl_level_mem_base_iff_iterate α hα m γ).mp hmem
  · intro hγ
    have hmem : g⁻¹ * z * g ∈ (iotaVertical α hα).range := by
      rw [hconj]
      exact (inl_level_mem_base_iff_iterate α hα m γ).mpr hγ
    have hinv := (iotaVertical α hα).range.inv_mem hmem
    simpa [mul_inv_rev, mul_assoc] using hinv

/-- The telescope acts on the HNN coset space through the left inclusion. -/
local instance telescopeCosetActionIterated :
    MulAction (Telescope α hα) (Cosets α hα) :=
  MulAction.compHom _ (inl : Telescope α hα →* Vertical α hα)

/-- The canonical equivalence from the base group onto telescope level `R`. -/
noncomputable def levelRangeEquiv (R : ℕ) : Γ ≃* (level α hα R).range :=
  MonoidHom.ofInjective (level_injective α hα R)

/-- The same level equivalence, precomposed with inner conjugation by `a`.
This parametrization makes the stabilizer of a common-level normal form equal
to an un-conjugated iterate of `α`. -/
noncomputable def conjugatedLevelEquiv (R : ℕ) (a : Γ) : Γ ≃* (level α hα R).range :=
  (MulAut.conj a).trans (levelRangeEquiv α hα R)

@[simp] theorem conjugatedLevelEquiv_coe (R : ℕ) (a γ : Γ) :
    (((conjugatedLevelEquiv α hα R a) γ : (level α hα R).range) :
      Telescope α hα) = level α hα R (a * γ * a⁻¹) := by
  simp [conjugatedLevelEquiv, levelRangeEquiv, MulAut.conj_apply,
    MonoidHom.ofInjective_apply, map_mul, map_inv]

/-- Every coset admits, above a sufficiently deep level, the normal form used
by the stabilizer computation. -/
theorem exists_site_level_threshold (x : Cosets α hα) :
    ∃ r : ℕ, ∀ R : ℕ, r ≤ R →
      ∃ (a : Γ) (k : ℤ) (m : ℕ),
        x = (inl (level α hα R a) * (tVertical α hα) ^ k) • rootCoset α hα ∧
        (m : ℤ) = (R : ℤ) + k := by
  classical
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x
  obtain ⟨n, y, hleft⟩ := exists_level_repr α hα g.left
  let k : ℤ := Multiplicative.toAdd g.right
  let r : ℕ := max n k.natAbs
  refine ⟨r, fun R hR => ?_⟩
  have hnR : n ≤ R := le_trans (le_max_left _ _) hR
  have hkR : k.natAbs ≤ R := le_trans (le_max_right _ _) hR
  have hnonneg : 0 ≤ (R : ℤ) + k := by
    have hklo : -(k.natAbs : ℤ) ≤ k := by
      rw [← Int.abs_eq_natAbs]
      exact neg_abs_le k
    have hkRz : (k.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast hkR
    omega
  have hmem : level α hα n y ∈ (level α hα R).range :=
    level_mem_range_of_le α hα hnR y
  obtain ⟨a, ha⟩ := hmem
  let m : ℕ := ((R : ℤ) + k).toNat
  have hm : (m : ℤ) = (R : ℤ) + k := by
    simp only [m]
    exact Int.toNat_of_nonneg hnonneg
  refine ⟨a, k, m, ?_, hm⟩
  have hleftR : g.left = level α hα R a :=
    hleft.symm.trans ha.symm
  have hsplit := vertical_eq_inl_mul_tVertical_zpow α hα g
  have hxg : x = g • rootCoset α hα := by
    rw [smul_rootCoset, hg]
  rw [hxg, hsplit, hleftR]

/-- A finite site window admits one common sufficiently deep normal-form level. -/
theorem exists_common_site_level (E : Finset (Cosets α hα)) :
    ∃ R : ℕ, ∀ x ∈ E,
      ∃ (a : Γ) (k : ℤ) (m : ℕ),
        x = (inl (level α hα R a) * (tVertical α hα) ^ k) • rootCoset α hα ∧
        (m : ℤ) = (R : ℤ) + k := by
  classical
  choose threshold hthreshold using fun x : Cosets α hα =>
    exists_site_level_threshold α hα x
  let R : ℕ := E.sup threshold
  refine ⟨R, fun x hx => ?_⟩
  exact hthreshold x R (Finset.le_sup (f := threshold) hx)

include hα in
/-- For a site in common-level normal form, the relevant stabilizer coset
action of the level subgroup is one of the iterated base coset actions. -/
theorem isSoficAction_level_stabilizer_of_iterates
    (hIter : IteratedCosetActionsSofic α)
    {R m : ℕ} {k : ℤ} (hm : (m : ℤ) = (R : ℤ) + k) (a : Γ)
    (x : Cosets α hα)
    (hx : x = (inl (level α hα R a) * (tVertical α hα) ^ k) •
      rootCoset α hα) :
    IsSoficAction ((level α hα R).range)
      (((level α hα R).range) ⧸
        MulAction.stabilizer ((level α hα R).range) x) := by
  classical
  let K : Subgroup (Telescope α hα) := (level α hα R).range
  change IsSoficAction K (K ⧸ MulAction.stabilizer K x)
  let ea : Γ ≃* K := conjugatedLevelEquiv α hα R a
  let Hm : Subgroup Γ := (iterateHom α m).range
  have hea : ∀ γ : Γ, ((ea γ : K) : Telescope α hα) =
      level α hα R (a * γ * a⁻¹) := by
    intro γ
    exact conjugatedLevelEquiv_coe α hα R a γ
  have hfix : ∀ γ : Γ,
      (ea γ : K) • x = x ↔ γ ∈ Hm := by
    intro γ
    rw [hx]
    change (inl ((ea γ : K) : Telescope α hα) : Vertical α hα) •
        ((inl (level α hα R a) * (tVertical α hα) ^ k) • rootCoset α hα)
      = ((inl (level α hα R a) * (tVertical α hα) ^ k) • rootCoset α hα) ↔ _
    rw [hea]
    exact conjugated_level_smul_site_iff α hα hm a γ
  have hstab : MulAction.stabilizer K x = Hm.map ea.toMonoidHom := by
    ext z
    obtain ⟨γ, rfl⟩ := ea.surjective z
    rw [MulAction.mem_stabilizer_iff, hfix]
    constructor
    · intro hγ
      exact Subgroup.mem_map_of_mem ea.toMonoidHom hγ
    · rintro ⟨δ, hδ, hEq⟩
      have : δ = γ := ea.injective hEq
      simpa [this] using hδ
  have htransport : IsSoficAction K (K ⧸ Hm.map ea.toMonoidHom) :=
    isSoficAction_quotient_map_mulEquiv ea Hm (hIter m)
  rw [hstab]
  exact htransport

include hα in
/-- Sufficiency on the telescope: the finite group and site windows can always
be moved to one common level, where the tested stabilizers are iterated
self-images of the base. -/
theorem isSoficAction_telescope_cosets_of_iterates
    (hIter : IteratedCosetActionsSofic α) :
    IsSoficAction (Telescope α hα) (Cosets α hα) := by
  classical
  refine isSoficAction_of_local_subgroup_models ?_
  intro F E ε hε
  obtain ⟨nF, hnF⟩ := exists_common_level_finset α hα F
  obtain ⟨nE, hnE⟩ := exists_common_site_level α hα E
  let R : ℕ := max nF nE
  let K : Subgroup (Telescope α hα) := (level α hα R).range
  have hFK : ∀ g ∈ F, g ∈ K := by
    intro g hg
    have hgN : g ∈ (level α hα nF).range := hnF g hg
    obtain ⟨y, rfl⟩ := hgN
    exact level_mem_range_of_le α hα (le_max_left _ _) y
  refine ⟨K, hFK, ?_⟩
  have hst : ∀ x ∈ E,
      IsSoficAction K (K ⧸ MulAction.stabilizer K x) := by
    intro x hxE
    obtain ⟨a, k, m, hx, hm⟩ := hnE x hxE
    have hraise : nE ≤ R := le_max_right _ _
    obtain ⟨b, hb⟩ := level_mem_range_of_le α hα hraise a
    have hxR : x = (inl (level α hα R b) * (tVertical α hα) ^ k) •
        rootCoset α hα := by
      rw [hx, ← hb]
    have hmRnonneg : 0 ≤ (R : ℤ) + k := by
      have hmnonneg : 0 ≤ (nE : ℤ) + k := by
        rw [← hm]
        exact_mod_cast Nat.zero_le m
      have hraiseZ : (nE : ℤ) ≤ (R : ℤ) := by exact_mod_cast hraise
      omega
    let mR : ℕ := ((R : ℤ) + k).toNat
    have hmR : (mR : ℤ) = (R : ℤ) + k := Int.toNat_of_nonneg hmRnonneg
    exact isSoficAction_level_stabilizer_of_iterates α hα hIter hmR b x hxR
  exact exists_model_of_window_stabilizers
    (finsetToSubgroup F K hFK) E ε hε hst

include hα in
/-- **Sufficiency.**  Soficity of every iterated base coset action implies
soficity of the full ascending-HNN coset action. -/
theorem isSoficAction_vertical_cosets_of_iterates
    (hIter : IteratedCosetActionsSofic α) :
    IsSoficAction (Vertical α hα) (Cosets α hα) := by
  classical
  haveI : DecidableEq (Cosets α hα) := Classical.decEq _
  exact isSoficAction_semidirect (fun _ _ => rfl)
    (isSoficAction_telescope_cosets_of_iterates α hα hIter)

/-! ## Necessity -/

include hα in
/-- The level-zero subgroup, at the site `t^m Γ`, has stabilizer the image of
`α^m`, after identifying level zero with `Γ`. -/
theorem levelZero_stabilizer_at_iterate_site (m : ℕ) :
    MulAction.stabilizer ((level α hα 0).range)
        ((tVertical α hα) ^ (m : ℤ) • rootCoset α hα)
      = ((iterateHom α m).range).map
          (levelRangeEquiv α hα 0).toMonoidHom := by
  classical
  let K : Subgroup (Telescope α hα) := (level α hα 0).range
  let e0 : Γ ≃* K := levelRangeEquiv α hα 0
  change MulAction.stabilizer K
        ((tVertical α hα) ^ (m : ℤ) • rootCoset α hα)
      = ((iterateHom α m).range).map e0.toMonoidHom
  ext z
  obtain ⟨γ, rfl⟩ := e0.surjective z
  have he0 : (((e0 γ : K) : Telescope α hα)) = level α hα 0 γ := rfl
  rw [MulAction.mem_stabilizer_iff]
  change (inl (((e0 γ : K) : Telescope α hα)) : Vertical α hα) •
      ((tVertical α hα) ^ (m : ℤ) • rootCoset α hα)
    = ((tVertical α hα) ^ (m : ℤ) • rootCoset α hα) ↔ _
  rw [he0]
  have hfix := conjugated_level_smul_site_iff α hα
    (R := 0) (m := m) (k := (m : ℤ)) (by simp) (1 : Γ) γ
  have hmap : γ ∈ (iterateHom α m).range ↔
      e0 γ ∈ ((iterateHom α m).range).map e0.toMonoidHom := by
    constructor
    · intro hγ
      exact Subgroup.mem_map_of_mem e0.toMonoidHom hγ
    · rintro ⟨δ, hδ, hEq⟩
      have hδγ : δ = γ := e0.injective hEq
      simpa [hδγ] using hδ
  rw [show (1 : Γ) * γ * (1 : Γ)⁻¹ = γ by simp] at hfix
  rw [map_one, map_one, one_mul] at hfix
  exact hfix.trans hmap

include hα in
/-- **Necessity.**  Soficity of the ascending-HNN coset action forces every
iterated base coset action to be sofic. -/
theorem iteratedCosetActionsSofic_of_vertical
    (hV : IsSoficAction (Vertical α hα) (Cosets α hα)) :
    IteratedCosetActionsSofic α := by
  classical
  have hTel : IsSoficAction (Telescope α hα) (Cosets α hα) :=
    IsSoficAction.compHom (inl : Telescope α hα →* Vertical α hα) hV
  intro m
  let K : Subgroup (Telescope α hα) := (level α hα 0).range
  let e0 : Γ ≃* K := levelRangeEquiv α hα 0
  have hK : IsSoficAction K (Cosets α hα) :=
    IsSoficAction.compHom K.subtype hTel
  let x : Cosets α hα := (tVertical α hα) ^ (m : ℤ) • rootCoset α hα
  have hOrbit : IsSoficAction K (K ⧸ MulAction.stabilizer K x) := by
    refine IsSoficAction.of_equivariant_injective (orbitMap x)
      (orbitMap_injective x) ?_ hK
    intro z q
    exact orbitMap_equivariant x z q
  have hstab := levelZero_stabilizer_at_iterate_site α hα m
  change MulAction.stabilizer K x = ((iterateHom α m).range).map e0.toMonoidHom at hstab
  rw [hstab] at hOrbit
  have hback : (((iterateHom α m).range).map e0.toMonoidHom).map
      e0.symm.toMonoidHom = (iterateHom α m).range := by
    rw [Subgroup.map_map]
    have hcomp : e0.symm.toMonoidHom.comp e0.toMonoidHom = MonoidHom.id Γ := by
      ext γ
      simp
    rw [hcomp, Subgroup.map_id]
  have hbackAction := isSoficAction_quotient_map_mulEquiv e0.symm
    (((iterateHom α m).range).map e0.toMonoidHom) hOrbit
  rw [hback] at hbackAction
  exact hbackAction

include hα in
/-- **Exact iterated-coset criterion.**  No additional ascending-HNN
obstruction remains after the tower of base coset actions is understood. -/
theorem isSoficAction_vertical_cosets_iff_iterates :
    IsSoficAction (Vertical α hα) (Cosets α hα) ↔
      IteratedCosetActionsSofic α :=
  ⟨iteratedCosetActionsSofic_of_vertical α hα,
    isSoficAction_vertical_cosets_of_iterates α hα⟩

include hα in
/-- A clean unconditional sufficient condition for Fournier-Facio's question:
if every iterated self-image is separable in the base group, then the
ascending-HNN coset action is sofic. -/
theorem isSoficAction_vertical_cosets_of_iteratedRangesSeparable
    (hsep : IteratedRangesSeparable α) :
    IsSoficAction (Vertical α hα) (Cosets α hα) :=
  isSoficAction_vertical_cosets_of_iterates α hα
    (iteratedCosetActionsSofic_of_iteratedRangesSeparable α hsep)

end MarkedCompression
end GroupApproximation
