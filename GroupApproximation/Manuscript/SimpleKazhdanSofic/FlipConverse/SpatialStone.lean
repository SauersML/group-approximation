import Mathlib
import GroupApproximation.Meta.AxiomGuard

/-!
# Spatial realization, part 2: Stone duality for clopen algebras

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds").  Step 3 of
the route to `SpatialRealizationStatement`.

Let `X`, `Y` be compact Hausdorff totally disconnected spaces and `θ : Set X → Set Y` a map
sending clopens to clopens, with `U ⊆ U' ↔ θ U ⊆ θ U'` for clopen `U, U'`, and onto the clopens
of `Y`.  Then there is a homeomorphism `h : X ≃ₜ Y` with `h x ∈ θ U ↔ x ∈ U` for every clopen `U`
(`exists_homeomorph_of_clopen_orderIso`).

* `θ ∅ = ∅`, `θ univ = univ`, `θ U ∩ θ U' ⊆ θ (U ∩ U')`, and `θ Uᶜ = (θ U)ᶜ`.
* `h x` is a point of `⋂_{x ∈ U clopen} θ U` (directed family of nonempty compact sets).
* Injective: clopens separate points of `X`.  Surjective: for `y`, a point `x` of
  `⋂_{y ∈ θ U} U` has `h x` and `y` in the same clopens `θ U`, so `h x = y`.
* Continuous: `h⁻¹ (θ U) = U` and clopens form a basis; a continuous bijection from a compact
  space to a Hausdorff space is a homeomorphism.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_isClopen_separating [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {x x' : X} (h : x ≠ x') : ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ x' ∉ U := by
  obtain ⟨U, hU, hxU, hUsub⟩ :=
    isTopologicalBasis_isClopen.mem_nhds_iff.1 (isOpen_compl_singleton.mem_nhds h)
  exact ⟨U, hU, hxU, fun hx' => hUsub hx' (Set.mem_singleton x')⟩

section Clopen

variable {θ : Set X → Set Y} (hθc : ∀ U, IsClopen U → IsClopen (θ U))
  (hθo : ∀ U U', IsClopen U → IsClopen U' → (U ⊆ U' ↔ θ U ⊆ θ U'))
  (hθs : ∀ V, IsClopen V → ∃ U, IsClopen U ∧ θ U = V)

include hθo hθs in
theorem clopenMap_empty : θ ∅ = ∅ := by
  obtain ⟨U0, hU0, hθU0⟩ := hθs ∅ isClopen_empty
  have h1 : θ ∅ ⊆ θ U0 := (hθo ∅ U0 isClopen_empty hU0).1 (Set.empty_subset U0)
  rw [hθU0] at h1
  exact Set.subset_empty_iff.1 h1

include hθo hθs in
theorem mem_clopenMap_univ (y : Y) : y ∈ θ Set.univ := by
  obtain ⟨U1, hU1, hθU1⟩ := hθs Set.univ isClopen_univ
  have h1 : θ U1 ⊆ θ Set.univ := (hθo U1 Set.univ hU1 isClopen_univ).1 (Set.subset_univ U1)
  rw [hθU1] at h1
  exact h1 (Set.mem_univ y)

include hθc hθo hθs in
theorem clopenMap_inter_subset {U U' : Set X} (hU : IsClopen U) (hU' : IsClopen U') :
    θ U ∩ θ U' ⊆ θ (U ∩ U') := by
  obtain ⟨U3, hU3, hθU3⟩ := hθs (θ U ∩ θ U') ((hθc U hU).inter (hθc U' hU'))
  have h1 : U3 ⊆ U := (hθo U3 U hU3 hU).2 (by rw [hθU3]; exact Set.inter_subset_left)
  have h2 : U3 ⊆ U' := (hθo U3 U' hU3 hU').2 (by rw [hθU3]; exact Set.inter_subset_right)
  have h3 : θ U3 ⊆ θ (U ∩ U') :=
    (hθo U3 (U ∩ U') hU3 (hU.inter hU')).1 (Set.subset_inter h1 h2)
  rw [hθU3] at h3
  exact h3

include hθc hθo hθs in
theorem notMem_clopenMap_compl {U : Set X} (hU : IsClopen U) {y : Y} (hy : y ∈ θ U) :
    y ∉ θ Uᶜ := by
  intro hy'
  have h1 := clopenMap_inter_subset hθc hθo hθs hU hU.compl ⟨hy, hy'⟩
  rw [Set.inter_compl_self, clopenMap_empty hθo hθs] at h1
  exact Set.notMem_empty y h1

include hθc hθo hθs in
theorem mem_clopenMap_compl {U : Set X} (hU : IsClopen U) {y : Y} (hy : y ∉ θ U) :
    y ∈ θ Uᶜ := by
  obtain ⟨U2, hU2, hθU2⟩ := hθs (θ U ∪ θ Uᶜ) ((hθc U hU).union (hθc Uᶜ hU.compl))
  have hsub1 : U ⊆ U2 := (hθo U U2 hU hU2).2 (by rw [hθU2]; exact Set.subset_union_left)
  have hsub2 : Uᶜ ⊆ U2 :=
    (hθo Uᶜ U2 hU.compl hU2).2 (by rw [hθU2]; exact Set.subset_union_right)
  have hU2univ : Set.univ ⊆ U2 := fun z _ => by
    by_cases hz : z ∈ U
    · exact hsub1 hz
    · exact hsub2 hz
  have h3 : θ Set.univ ⊆ θ U2 := (hθo Set.univ U2 isClopen_univ hU2).1 hU2univ
  rw [hθU2] at h3
  rcases h3 (mem_clopenMap_univ hθo hθs y) with h4 | h4
  · exact absurd h4 hy
  · exact h4

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
  [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]

include hθc hθo hθs in
/-- Stone duality: an order isomorphism of clopen algebras is induced by a homeomorphism. -/
theorem exists_homeomorph_of_clopen_orderIso :
    ∃ h : X ≃ₜ Y, ∀ (x : X) (U : Set X), IsClopen U → (h x ∈ θ U ↔ x ∈ U) := by
  have hpt : ∀ x : X, ∃ y : Y, ∀ U, IsClopen U → (y ∈ θ U ↔ x ∈ U) := by
    intro x
    haveI : Nonempty {U : Set X // IsClopen U ∧ x ∈ U} :=
      ⟨⟨Set.univ, isClopen_univ, Set.mem_univ x⟩⟩
    have hdir : Directed (· ⊇ ·) (fun i : {U : Set X // IsClopen U ∧ x ∈ U} => θ i.1) := by
      rintro ⟨U, hU, hxU⟩ ⟨U', hU', hxU'⟩
      refine ⟨⟨U ∩ U', hU.inter hU', hxU, hxU'⟩, ?_, ?_⟩
      · exact (hθo (U ∩ U') U (hU.inter hU') hU).1 Set.inter_subset_left
      · exact (hθo (U ∩ U') U' (hU.inter hU') hU').1 Set.inter_subset_right
    have hne : ∀ i : {U : Set X // IsClopen U ∧ x ∈ U}, (θ i.1).Nonempty := by
      intro i
      by_contra hempty
      have h2 : θ i.1 ⊆ θ ∅ := fun z hz => (hempty ⟨z, hz⟩).elim
      exact Set.notMem_empty x ((hθo i.1 ∅ i.2.1 isClopen_empty).2 h2 i.2.2)
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun i : {U : Set X // IsClopen U ∧ x ∈ U} => θ i.1) hdir hne
      (fun i => (hθc i.1 i.2.1).isClosed.isCompact) (fun i => (hθc i.1 i.2.1).isClosed)
    refine ⟨y, fun U hU => ⟨fun hyU => ?_, fun hxU => Set.mem_iInter.1 hy ⟨U, hU, hxU⟩⟩⟩
    by_contra hxU
    have h1 : y ∈ θ Uᶜ := Set.mem_iInter.1 hy ⟨Uᶜ, hU.compl, hxU⟩
    exact notMem_clopenMap_compl hθc hθo hθs hU hyU h1
  choose hfun hf using hpt
  have hinj : Function.Injective hfun := by
    intro x x' hxx'
    by_contra hne
    obtain ⟨U, hU, hxU, hx'U⟩ := exists_isClopen_separating hne
    have h1 : hfun x' ∈ θ U := by
      rw [← hxx']
      exact (hf x U hU).2 hxU
    exact hx'U ((hf x' U hU).1 h1)
  have hsurj : Function.Surjective hfun := by
    intro y
    have hpt' : ∃ x : X, ∀ U, IsClopen U → y ∈ θ U → x ∈ U := by
      haveI : Nonempty {U : Set X // IsClopen U ∧ y ∈ θ U} :=
        ⟨⟨Set.univ, isClopen_univ, mem_clopenMap_univ hθo hθs y⟩⟩
      have hdir : Directed (· ⊇ ·) (fun i : {U : Set X // IsClopen U ∧ y ∈ θ U} => i.1) := by
        rintro ⟨U, hU, hyU⟩ ⟨U', hU', hyU'⟩
        exact ⟨⟨U ∩ U', hU.inter hU', clopenMap_inter_subset hθc hθo hθs hU hU' ⟨hyU, hyU'⟩⟩,
          Set.inter_subset_left, Set.inter_subset_right⟩
      have hne : ∀ i : {U : Set X // IsClopen U ∧ y ∈ θ U}, (i.1).Nonempty := by
        intro i
        by_contra hempty
        have h1 : y ∈ θ i.1 := i.2.2
        rw [Set.not_nonempty_iff_eq_empty.1 hempty, clopenMap_empty hθo hθs] at h1
        exact Set.notMem_empty y h1
      obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        (fun i : {U : Set X // IsClopen U ∧ y ∈ θ U} => i.1) hdir hne
        (fun i => i.2.1.isClosed.isCompact) (fun i => i.2.1.isClosed)
      exact ⟨x, fun U hU hyU => Set.mem_iInter.1 hx ⟨U, hU, hyU⟩⟩
    obtain ⟨x, hx⟩ := hpt'
    refine ⟨x, ?_⟩
    by_contra hne
    obtain ⟨V, hV, hfxV, hyV⟩ := exists_isClopen_separating hne
    obtain ⟨U, hU, rfl⟩ := hθs V hV
    have hxU : x ∈ U := (hf x U hU).1 hfxV
    exact (hx Uᶜ hU.compl (mem_clopenMap_compl hθc hθo hθs hU hyV)) hxU
  have hcont : Continuous hfun := by
    refine (isTopologicalBasis_isClopen (X := Y)).continuous_iff.2 fun V hV => ?_
    obtain ⟨U, hU, rfl⟩ := hθs V hV
    have hpre : hfun ⁻¹' θ U = U := Set.ext fun x => hf x U hU
    rw [hpre]
    exact hU.isOpen
  exact ⟨hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective hfun ⟨hinj, hsurj⟩), hf⟩

end Clopen

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_isClopen_separating
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.mem_clopenMap_compl
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_homeomorph_of_clopen_orderIso
