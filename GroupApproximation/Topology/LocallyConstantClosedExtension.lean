import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Separation.Profinite

/-!
# Locally constant functions on a closed subset extend

`non_mf_groups_exist.tex`, `\label{lem:transient-matrices}`, proof, tex 1482–1484:

> Locally constant functions on a closed subset extend by finite
> clopen partitions.  Their restriction kernel consists exactly of
> functions compactly supported in the complement.

The space `X` is compact, Hausdorff and totally disconnected, and `Y ⊆ X` is closed.

* `exists_isClopen_preimage_val_eq`: a clopen subset of `Y` is the trace on `Y` of a clopen subset
  of `X`;
* `LocallyConstant.exists_comap_val_eq_of_isClosed`: every `f : LC(Y, Z)` is the restriction of
  some `g : LC(X, Z)`.  The extension is read from clopen traces of the finitely many level sets
  of `f`, so it is constant on the atoms of a finite clopen partition of `X`;
* `restrictRingHom Y : LC(X, k) →+* LC(Y, k)` and `restrictRingHom_surjective`;
* `comap_val_eq_zero_iff_support_subset_compl`: `g` restricts to `0` exactly when its support lies
  in `X ∖ Y`;
* `isClopen_support` and `isCompact_support`: that support is clopen, hence compact.
-/

namespace GroupApproximation.ChainCore

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- Restriction `LC(X, k) → LC(Y, k)` to a subset `Y ⊆ X`, as a ring homomorphism. -/
def restrictRingHom {k : Type*} [Semiring k] (Y : Set X) :
    LocallyConstant X k →+* LocallyConstant Y k :=
  LocallyConstant.comapRingHom ⟨Subtype.val, continuous_subtype_val⟩

theorem restrictRingHom_apply {k : Type*} [Semiring k] (Y : Set X) (g : LocallyConstant X k) :
    restrictRingHom Y g = g.comap ⟨Subtype.val, continuous_subtype_val⟩ :=
  rfl

/-- **The restriction kernel** (tex 1483–1484): `g` restricts to `0` on `Y` exactly when its
support lies in the complement of `Y`. -/
theorem comap_val_eq_zero_iff_support_subset_compl {k : Type*} [Zero k] {Y : Set X}
    (g : LocallyConstant X k) :
    g.comap (⟨Subtype.val, continuous_subtype_val⟩ : C(Y, X)) = 0 ↔ Function.support g ⊆ Yᶜ := by
  constructor
  · intro h x hx hxY
    exact hx (congrArg (fun f : LocallyConstant Y k => f ⟨x, hxY⟩) h)
  · intro h
    ext y
    by_contra hy
    have hy' : (y : X) ∈ Function.support g := hy
    exact h hy' y.2

/-- The support of a locally constant function is clopen. -/
theorem isClopen_support {k : Type*} [Zero k] (g : LocallyConstant X k) :
    IsClopen (Function.support g) := by
  have h : Function.support g = {x | g x = 0}ᶜ := Set.ext fun _ => Iff.rfl
  rw [h]
  exact (g.isLocallyConstant.isClopen_fiber 0).compl

/-- The support of a locally constant function on a compact space is compact. -/
theorem isCompact_support [CompactSpace X] {k : Type*} [Zero k] (g : LocallyConstant X k) :
    IsCompact (Function.support g) :=
  (isClopen_support g).1.isCompact

section Profinite

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

/-- A clopen subset of a closed `Y ⊆ X` is the trace on `Y` of a clopen subset of `X`. -/
theorem exists_isClopen_preimage_val_eq {Y : Set X} (hY : IsClosed Y) {F : Set Y}
    (hF : IsClopen F) : ∃ W : Set X, IsClopen W ∧ Subtype.val ⁻¹' W = F := by
  haveI : CompactSpace Y := isCompact_iff_compactSpace.mp hY.isCompact
  have hFc : IsCompact (Subtype.val '' F) := hF.1.isCompact.image continuous_subtype_val
  have hG : IsClosed (Subtype.val '' Fᶜ) :=
    (hF.2.isClosed_compl.isCompact.image continuous_subtype_val).isClosed
  -- each point of the image of `F` has a clopen neighbourhood missing the image of `Y ∖ F`
  have hloc : ∀ x ∈ Subtype.val '' F,
      ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ (Subtype.val '' Fᶜ)ᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    refine compact_exists_isClopen_in_isOpen hG.isOpen_compl ?_
    rintro ⟨y, hy, hyz⟩
    obtain rfl := Subtype.val_injective hyz
    exact hy hz
  choose! V hV hxV hVG using hloc
  obtain ⟨t, htF, hcover⟩ :=
    hFc.elim_nhds_subcover V fun x hx => (hV x hx).2.mem_nhds (hxV x hx)
  refine ⟨⋃ x ∈ t, V x, isClopen_biUnion_finset fun x hx => hV x (htF x hx), ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨x, hx, hyV⟩
    by_contra hy
    exact hVG x (htF x hx) hyV ⟨y, hy, rfl⟩
  · intro hy
    simpa only [Set.mem_iUnion, exists_prop] using hcover (Set.mem_image_of_mem Subtype.val hy)

/-- **Extension** (tex 1482–1483): a locally constant function on a closed `Y ⊆ X` is the
restriction of a locally constant function on `X`.  Its value at `x` is chosen among the finitely
many values `v` of `f` whose level set has a clopen trace containing `x`. -/
theorem LocallyConstant.exists_comap_val_eq_of_isClosed {Z : Type*} [Nonempty Z] {Y : Set X}
    (hY : IsClosed Y) (f : LocallyConstant Y Z) :
    ∃ g : LocallyConstant X Z, g.comap ⟨Subtype.val, continuous_subtype_val⟩ = f := by
  classical
  haveI : CompactSpace Y := isCompact_iff_compactSpace.mp hY.isCompact
  let vals : Finset Z := f.range_finite.toFinset
  have htrace : ∀ v : Z, ∃ W : Set X, IsClopen W ∧ Subtype.val ⁻¹' W = {y : Y | f y = v} :=
    fun v => exists_isClopen_preimage_val_eq hY (f.isLocallyConstant.isClopen_fiber v)
  choose W hW hWY using htrace
  let S : X → Finset Z := fun x => vals.filter fun v => x ∈ W v
  have hS : IsLocallyConstant S := by
    refine (IsLocallyConstant.iff_eventually_eq S).2 fun x => ?_
    have h : ∀ v ∈ vals, ∀ᶠ y in 𝓝 x, (y ∈ W v ↔ x ∈ W v) := by
      intro v _
      by_cases hx : x ∈ W v
      · filter_upwards [(hW v).2.mem_nhds hx] with y hy
        exact ⟨fun _ => hx, fun _ => hy⟩
      · filter_upwards [(hW v).1.isOpen_compl.mem_nhds hx] with y hy
        exact ⟨fun h => (hy h).elim, fun h => (hx h).elim⟩
    filter_upwards [(Filter.eventually_all_finset vals).2 h] with y hy
    ext v
    simp only [S, Finset.mem_filter]
    exact and_congr_right fun hv => hy v hv
  let pick : Finset Z → Z := fun s => Classical.epsilon fun v => v ∈ s
  refine ⟨⟨pick ∘ S, hS.comp pick⟩, ?_⟩
  ext y
  have hWy : ∀ v, (y : X) ∈ W v ↔ f y = v := fun v => Set.ext_iff.mp (hWY v) y
  have hSy : S (y : X) = {f y} := by
    ext v
    simp only [S, Finset.mem_filter, Finset.mem_singleton, hWy]
    constructor
    · rintro ⟨-, rfl⟩
      rfl
    · rintro rfl
      exact ⟨f.range_finite.mem_toFinset.2 (Set.mem_range_self y), rfl⟩
  show pick (S (y : X)) = f y
  rw [hSy]
  exact Finset.mem_singleton.mp (Classical.epsilon_spec (p := fun v => v ∈ ({f y} : Finset Z))
    ⟨f y, Finset.mem_singleton_self _⟩)

/-- **Surjectivity of restriction** (tex 1482–1483). -/
theorem restrictRingHom_surjective {k : Type*} [Semiring k] {Y : Set X} (hY : IsClosed Y) :
    Function.Surjective (restrictRingHom (k := k) Y) := by
  intro f
  obtain ⟨g, hg⟩ := LocallyConstant.exists_comap_val_eq_of_isClosed hY f
  exact ⟨g, hg⟩

end Profinite

#audit_axioms GroupApproximation.ChainCore.restrictRingHom_apply
#audit_axioms GroupApproximation.ChainCore.comap_val_eq_zero_iff_support_subset_compl
#audit_axioms GroupApproximation.ChainCore.isClopen_support
#audit_axioms GroupApproximation.ChainCore.isCompact_support
#audit_axioms GroupApproximation.ChainCore.exists_isClopen_preimage_val_eq
#audit_axioms GroupApproximation.ChainCore.LocallyConstant.exists_comap_val_eq_of_isClosed
#audit_axioms GroupApproximation.ChainCore.restrictRingHom_surjective

end GroupApproximation.ChainCore
