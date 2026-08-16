import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The finite residual

Sections 42.5, 49.4 and 50.1 of the ascending-HNN dossier, in their purely
group-theoretic form.

`finiteResidual G` is the intersection of **all** finite-index subgroups of `G`,
not merely the normal ones.  Three facts are proved:

* `finiteResidual_eq_normalFiniteResidual` — Lemma 42.7: intersecting all
  finite-index subgroups gives the same subgroup as intersecting only the normal
  ones, because a finite-index subgroup contains its finite-index normal core.
  Consequently the finite residual really is the kernel of the profinite
  completion map.
* `map_finiteResidual_le` — Lemma 50.1: the finite residual is functorial, hence
  fully invariant; every endomorphism of `G` maps it into itself.
* `mem_finiteResidual_subgroup_iff` — Lemma 49.4: for a finite-index subgroup,
  the finite residual is exactly the trace of the ambient one.  This is the
  group-theoretic half of the statement that no passage to finite index can
  repair approximation failure.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- The intersection of all finite-index subgroups. -/
def finiteResidual (G : Type u) [Group G] : Subgroup G :=
  sInf {L : Subgroup G | L.FiniteIndex}

/-- The intersection of all finite-index normal subgroups. -/
def normalFiniteResidual (G : Type u) [Group G] : Subgroup G :=
  sInf {L : Subgroup G | L.Normal ∧ L.FiniteIndex}

theorem mem_finiteResidual_iff {x : G} :
    x ∈ finiteResidual G ↔ ∀ L : Subgroup G, L.FiniteIndex → x ∈ L := by
  simp [finiteResidual, Subgroup.mem_sInf]

theorem mem_normalFiniteResidual_iff {x : G} :
    x ∈ normalFiniteResidual G ↔
      ∀ L : Subgroup G, L.Normal → L.FiniteIndex → x ∈ L := by
  simp [normalFiniteResidual, Subgroup.mem_sInf, and_imp]

/-- **Lemma 42.7.**  Intersecting all finite-index subgroups is the same as
intersecting only the finite-index normal ones. -/
theorem finiteResidual_eq_normalFiniteResidual :
    finiteResidual G = normalFiniteResidual G := by
  refine le_antisymm ?_ ?_
  · rw [SetLike.le_def]
    intro x hx
    rw [mem_normalFiniteResidual_iff]
    intro L _ hf
    exact mem_finiteResidual_iff.mp hx L hf
  · rw [SetLike.le_def]
    intro x hx
    rw [mem_finiteResidual_iff]
    intro L hL
    haveI := hL
    have hcore : x ∈ L.normalCore :=
      mem_normalFiniteResidual_iff.mp hx L.normalCore inferInstance inferInstance
    exact L.normalCore_le hcore

/-- The preimage of a finite-index **normal** subgroup has finite index. -/
theorem finiteIndex_comap_of_normal (f : G →* H) (N : Subgroup H) [N.Normal]
    [N.FiniteIndex] : (N.comap f).FiniteIndex := by
  classical
  haveI : Finite (H ⧸ N) := N.finite_quotient_of_finiteIndex
  set ψ : G →* (H ⧸ N) := (QuotientGroup.mk' N).comp f with hψ
  have hker : ψ.ker = N.comap f := by
    ext x
    simp [hψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  haveI : Finite ψ.range := Subtype.finite
  haveI : Finite (G ⧸ ψ.ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).symm.toEquiv
  refine ⟨?_⟩
  rw [← hker, Subgroup.index_eq_card]
  exact Nat.card_pos.ne'

/-- **Lemma 50.1.**  The finite residual is functorial: every homomorphism maps
it into the finite residual of the target.  In particular it is fully invariant,
hence characteristic. -/
theorem map_finiteResidual_le (f : G →* H) :
    (finiteResidual G).map f ≤ finiteResidual H := by
  rw [SetLike.le_def]
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_finiteResidual_iff]
  intro L hL
  haveI := hL
  haveI : (L.normalCore.comap f).FiniteIndex :=
    finiteIndex_comap_of_normal f L.normalCore
  have hmem := mem_finiteResidual_iff.mp hx (L.normalCore.comap f) inferInstance
  rw [Subgroup.mem_comap] at hmem
  exact L.normalCore_le hmem

/-- One half of Lemma 49.4, valid for an **arbitrary** subgroup: the finite
residual of a subgroup lands inside the ambient finite residual. -/
theorem coe_mem_finiteResidual_of_mem {K : Subgroup G} (x : K)
    (hx : x ∈ finiteResidual K) : (x : G) ∈ finiteResidual G := by
  rw [mem_finiteResidual_iff]
  intro L hL
  haveI := hL
  haveI : (L.subgroupOf K).FiniteIndex := Subgroup.instFiniteIndex_subgroupOf L K
  have := mem_finiteResidual_iff.mp hx (L.subgroupOf K) inferInstance
  simpa [Subgroup.mem_subgroupOf] using this

/-- **Lemma 49.4.**  For a finite-index subgroup the finite residual is exactly
the trace of the ambient finite residual. -/
theorem mem_finiteResidual_subgroup_iff {K : Subgroup G} [K.FiniteIndex]
    (x : K) : x ∈ finiteResidual K ↔ (x : G) ∈ finiteResidual G := by
  constructor
  · exact coe_mem_finiteResidual_of_mem x
  · intro hx
    rw [mem_finiteResidual_iff]
    intro M hM
    haveI := hM
    set L : Subgroup G := M.map K.subtype with hLdef
    have hLK : L ≤ K := by
      rw [hLdef]
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hsub : L.subgroupOf K = M := by
      rw [hLdef, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    have hrel : L.relIndex K = M.index := by
      rw [Subgroup.relIndex, hsub]
    haveI : L.FiniteIndex := by
      refine ⟨?_⟩
      have := Subgroup.relIndex_mul_index hLK
      rw [hrel] at this
      rw [← this]
      exact Nat.mul_ne_zero Subgroup.FiniteIndex.index_ne_zero
        Subgroup.FiniteIndex.index_ne_zero
    have hxL : (x : G) ∈ L := mem_finiteResidual_iff.mp hx L inferInstance
    rw [← hsub]
    simpa [Subgroup.mem_subgroupOf] using hxL

/-! ## Residual finiteness -/

/-- A group is residually finite exactly when its finite residual is trivial. -/
def IsResiduallyFinite (G : Type u) [Group G] : Prop := finiteResidual G = ⊥

theorem isResiduallyFinite_iff :
    IsResiduallyFinite G ↔
      ∀ x : G, x ≠ 1 → ∃ L : Subgroup G, L.FiniteIndex ∧ x ∉ L := by
  constructor
  · intro h x hx
    by_contra hcon
    push Not at hcon
    have : x ∈ finiteResidual G :=
      mem_finiteResidual_iff.mpr fun L hL => hcon L hL
    rw [h, Subgroup.mem_bot] at this
    exact hx this
  · intro h
    refine le_antisymm ?_ bot_le
    rw [SetLike.le_def]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨L, hL, hnot⟩ := h x hx1
    exact hnot (mem_finiteResidual_iff.mp hx L hL)

/-- Residual finiteness passes to every subgroup. -/
theorem IsResiduallyFinite.subgroup (h : IsResiduallyFinite G) (K : Subgroup G) :
    IsResiduallyFinite K := by
  refine le_antisymm ?_ bot_le
  rw [SetLike.le_def]
  intro x hx
  rw [Subgroup.mem_bot]
  have hcoe : (x : G) ∈ finiteResidual G := coe_mem_finiteResidual_of_mem x hx
  rw [h, Subgroup.mem_bot] at hcoe
  exact Subtype.ext hcoe

/-- **Lemma 46.5.**  A group with a residually finite subgroup of finite index
is residually finite.  Together with the previous lemma, residual finiteness is
an abstract-commensurability invariant. -/
theorem isResiduallyFinite_of_finiteIndex_subgroup {K : Subgroup G}
    [K.FiniteIndex] (h : IsResiduallyFinite K) : IsResiduallyFinite G := by
  refine le_antisymm ?_ bot_le
  rw [SetLike.le_def]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxK : x ∈ K := mem_finiteResidual_iff.mp hx K inferInstance
  have : (⟨x, hxK⟩ : K) ∈ finiteResidual K :=
    (mem_finiteResidual_subgroup_iff (⟨x, hxK⟩ : K)).mpr hx
  rw [h, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

end GroupApproximation
