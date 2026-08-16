import GroupApproximation.Sofic.ProductMultiplicity

/-!
# Continuum multiplicity of the non-MF phenomenon

`Sofic.ProductMultiplicity` formalizes the first multiplicity sense of the
manuscript, the family `E × ℤ^k`.  The second pairs `E` with a continuum
of pairwise nonisomorphic two-generator groups and concludes that there are
`2^{ℵ₀}` pairwise nonisomorphic finitely generated non-MF groups.

The existence of such a continuum family is B. H. Neumann's, and it is not
proved here: it enters as a hypothesis, quantified visibly, exactly as the
routing datum does for the full-MF-radical endpoints.  What *is* proved
here is the manuscript's own argument on top of it, which is a counting
step: a fixed countable group is isomorphic to `E × N` for only countably
many of the types `N`, because each such `N` embeds in it as a finitely
generated subgroup and a countable group has only countably many of those.

That is the whole content of the sentence "a map with countable fibres
from a continuum-sized family has continuum-sized image": the products need
not be pairwise nonisomorphic, and the counting is what recovers a
continuum of distinct types from a family that might a priori collapse.
-/

namespace GroupApproximation
namespace ContinuumMultiplicity

open ProductMultiplicity ChosenMarkedPresentation

/-! ## Countability inputs -/

/-- A finitely generated group is countable: it is the image of the free
group on a finite generating set. -/
theorem countable_of_fg (N : Type) [Group N] [Group.FG N] : Countable N := by
  classical
  obtain ⟨S, hgen, hfin⟩ := Group.fg_iff.mp ‹Group.FG N›
  haveI : Finite S := hfin.to_subtype
  set f : FreeGroup S →* N := FreeGroup.lift fun s : S ↦ (s : N) with hf
  have hle : Subgroup.closure S ≤ f.range := by
    rw [Subgroup.closure_le]
    rintro x hx
    exact ⟨FreeGroup.of ⟨x, hx⟩, by simp [hf]⟩
  have hsurj : Function.Surjective f := by
    intro g
    have hg : g ∈ Subgroup.closure S := by rw [hgen]; exact Subgroup.mem_top g
    exact hle hg
  exact hsurj.countable

/-- A countable group has only countably many finitely generated
subgroups: every one of them is the closure of a finite subset. -/
theorem countable_fg_subgroups (X : Type) [Group X] [Countable X] :
    {H : Subgroup X | H.FG}.Countable := by
  classical
  have hsub : {H : Subgroup X | H.FG} ⊆
      Set.range fun s : Finset X ↦ Subgroup.closure (s : Set X) := by
    rintro H ⟨s, hs⟩
    exact ⟨s, hs⟩
  exact (Set.countable_range _).mono hsub

/-- The direct product of two finitely generated groups is finitely
generated: the two images of generating sets generate, because the factor
inclusions carry closures to closures. -/
theorem fg_prod {G H : Type} [Group G] [Group H] [Group.FG G] [Group.FG H] :
    Group.FG (G × H) := by
  classical
  obtain ⟨SG, hSG, hSGfin⟩ := Group.fg_iff.mp ‹Group.FG G›
  obtain ⟨SH, hSH, hSHfin⟩ := Group.fg_iff.mp ‹Group.FG H›
  set T : Set (G × H) :=
    (fun g : G ↦ ((g, 1) : G × H)) '' SG ∪ (fun h : H ↦ ((1, h) : G × H)) '' SH
    with hT
  refine Group.fg_iff.mpr ⟨T, ?_, (hSGfin.image _).union (hSHfin.image _)⟩
  rw [eq_top_iff]
  rintro ⟨g, h⟩ -
  have hgmem : ((g, 1) : G × H) ∈ Subgroup.closure T := by
    have hmap : Subgroup.map (MonoidHom.inl G H) (Subgroup.closure SG) ≤
        Subgroup.closure T := by
      rw [MonoidHom.map_closure]
      exact Subgroup.closure_mono Set.subset_union_left
    exact hmap ⟨g, by rw [hSG]; exact Subgroup.mem_top g, rfl⟩
  have hhmem : ((1, h) : G × H) ∈ Subgroup.closure T := by
    have hmap : Subgroup.map (MonoidHom.inr G H) (Subgroup.closure SH) ≤
        Subgroup.closure T := by
      rw [MonoidHom.map_closure]
      exact Subgroup.closure_mono Set.subset_union_right
    exact hmap ⟨h, by rw [hSH]; exact Subgroup.mem_top h, rfl⟩
  have : ((g, 1) : G × H) * (1, h) = (g, h) := by simp
  rw [← this]
  exact mul_mem hgmem hhmem

/-! ## The counting step -/

variable {ι : Type} (N : ι → Type) [∀ i, Group (N i)] [∀ i, Group.FG (N i)]

/-- Each member of the family embeds in any group isomorphic to its
product with `E`, as a finitely generated subgroup. -/
theorem exists_fg_subgroup_mulEquiv {X : Type} [Group X] {i : ι}
    (e : X ≃* (MarkedGroup × N i)) :
    ∃ H : Subgroup X, H.FG ∧ Nonempty (N i ≃* H) := by
  classical
  set f : N i →* X :=
    (e.symm : (MarkedGroup × N i) →* X).comp (MonoidHom.inr MarkedGroup (N i))
    with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have := e.symm.injective.eq_iff.mp hab
    simpa using congrArg Prod.snd this
  refine ⟨f.range, ?_, ⟨MonoidHom.ofInjective hinj⟩⟩
  exact (Group.fg_iff_subgroup_fg f.range).mp inferInstance

/-- **The manuscript's counting step.**  A fixed countable group is
isomorphic to `E × N i` for only countably many indices `i`, when the
family is pairwise nonisomorphic. -/
theorem countable_isomorphic_indices
    (hfam : ∀ i j : ι, Nonempty (N i ≃* N j) → i = j)
    (X : Type) [Group X] [Countable X] :
    {i : ι | Nonempty (X ≃* (MarkedGroup × N i))}.Countable := by
  classical
  set S : Set ι := {i : ι | Nonempty (X ≃* (MarkedGroup × N i))} with hS
  have hchoice : ∀ i : S, ∃ H : Subgroup X, H.FG ∧ Nonempty (N i ≃* H) := by
    rintro ⟨i, hi⟩
    obtain ⟨e⟩ := hi
    exact exists_fg_subgroup_mulEquiv N e
  choose H hHfg hHequiv using hchoice
  have hinj : Function.Injective fun i : S ↦ (⟨H i, hHfg i⟩ : {K : Subgroup X | K.FG}) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    have hHeq : H ⟨i, hi⟩ = H ⟨j, hj⟩ := congrArg Subtype.val hij
    obtain ⟨ei⟩ := hHequiv ⟨i, hi⟩
    obtain ⟨ej⟩ := hHequiv ⟨j, hj⟩
    have : Nonempty (N i ≃* N j) :=
      ⟨ei.trans ((MulEquiv.subgroupCongr hHeq).trans ej.symm)⟩
    exact Subtype.ext (hfam i j this)
  haveI : Countable {K : Subgroup X | K.FG} :=
    (countable_fg_subgroups X).to_subtype
  haveI : Countable S := hinj.countable
  exact Set.countable_coe_iff.mp inferInstance

/-! ## The family that results -/

/-- Every member of the enlarged family is finitely generated and not
operator-MF, by heredity through the first factor. -/
theorem product_fg_not_isOperatorMF (i : ι) :
    Group.FG (MarkedGroup × N i) ∧ ¬ IsOperatorMF (MarkedGroup × N i) := by
  haveI : Group.FG MarkedGroup :=
    ProductFinitePresentation.fg_of_isFinitelyPresented MarkedGroup
  refine ⟨fg_prod, ?_⟩
  intro hMF
  refine ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF.2 ?_
  refine IsOperatorMF.comap hMF (MonoidHom.inl MarkedGroup (N i)) ?_
  intro a b hab
  simpa using congrArg Prod.fst hab

end ContinuumMultiplicity
end GroupApproximation
