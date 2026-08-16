import GroupApproximation.Sofic.ProductMultiplicity
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Continuum multiplicity of the non-MF phenomenon: the counting step

`Sofic.ProductMultiplicity` formalizes the first multiplicity sense of the
manuscript, the family `E × ℤ^k`.  The second pairs `E` with a continuum
of pairwise nonisomorphic finitely generated groups and concludes that there
are `2^{ℵ₀}` pairwise nonisomorphic finitely generated non-MF groups.

What is proved here is the manuscript's own argument on top of such a family,
which is a counting step: a fixed countable group is isomorphic to `E × N` for
only countably many of the types `N`, because each such `N` embeds in it as a
finitely generated subgroup and a countable group has only countably many of
those.

That is the whole content of the sentence "a map with countable fibres
from a continuum-sized family has continuum-sized image": the products need
not be pairwise nonisomorphic, and the counting is what recovers a
continuum of distinct types from a family that might a priori collapse.

## Why this file exists separately

The family itself is *not* a hypothesis of the development.  It is constructed,
in `Monsters/NeumannAlternatingFamily` and `Monsters/NeumannContinuum`, as a
lamplighter over the coset spaces of the free group.  The badged declaration
`ContinuumMultiplicity.manuscriptContinuumMultiplicity` therefore states the
unconditional conclusion, and to do that it has to sit *downstream* of that
construction — which in turn consumes the counting step below.

So the counting step lives here, one level up, and keeps the namespace
`ContinuumMultiplicity`: callers write `ContinuumMultiplicity.countable_of_fg`
and `ContinuumMultiplicity.exists_continuum_pairwise_nonisomorphic` exactly as
before, and only the `import` line moves.
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

/-! ## Continuum many isomorphism types -/

/-- **Continuum multiplicity.**  Given a continuum-sized family of pairwise
nonisomorphic finitely generated groups -- B. H. Neumann's family is the
classical source, and it is a hypothesis here, not a theorem -- the
products with `E` contain a continuum-sized subfamily that is pairwise
nonisomorphic, and every member is finitely generated and not
operator-MF.

The subfamily is needed: the products themselves are not obviously
pairwise nonisomorphic, and the counting step is what recovers a continuum
of distinct types from fibres that are merely countable. -/
theorem exists_continuum_pairwise_nonisomorphic
    (hfam : ∀ i j : ι, Nonempty (N i ≃* N j) → i = j)
    (hcard : Cardinal.mk ι = Cardinal.continuum) :
    ∃ J : Set ι, Cardinal.mk J = Cardinal.continuum ∧
      (∀ i ∈ J, Group.FG (MarkedGroup × N i) ∧
        ¬ IsOperatorMF (MarkedGroup × N i)) ∧
      ∀ i ∈ J, ∀ j ∈ J,
        Nonempty ((MarkedGroup × N i) ≃* (MarkedGroup × N j)) → i = j := by
  classical
  haveI : ∀ i : ι, Countable (N i) := fun i ↦ countable_of_fg (N i)
  -- being isomorphic after multiplying by `E` is an equivalence on indices
  let s : Setoid ι :=
    { r := fun i j ↦ Nonempty ((MarkedGroup × N i) ≃* (MarkedGroup × N j))
      iseqv :=
        { refl := fun _ ↦ ⟨MulEquiv.refl _⟩
          symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
          trans := fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩ } }
  -- every class is countable, by the counting step
  have hclass : ∀ q : Quotient s, {i : ι | Quotient.mk s i = q}.Countable := by
    intro q
    have hEq : {i : ι | Quotient.mk s i = q} =
        {i : ι | Nonempty ((MarkedGroup × N q.out) ≃* (MarkedGroup × N i))} := by
      ext i
      constructor
      · intro hi
        exact Quotient.exact ((Quotient.out_eq q).trans hi.symm)
      · intro hi
        exact ((Quotient.sound hi).symm).trans (Quotient.out_eq q)
    rw [hEq]
    exact countable_isomorphic_indices N hfam (MarkedGroup × N q.out)
  haveI hcq : ∀ q : Quotient s, Countable {i : ι | Quotient.mk s i = q} :=
    fun q ↦ (hclass q).to_subtype
  -- countable fibres over the quotient bound the index set
  have huniv : (Set.univ : Set ι) =
      ⋃ q : Quotient s, {i : ι | Quotient.mk s i = q} := by
    ext i
    simp
  have hle : Cardinal.mk ι ≤ Cardinal.mk (Quotient s) * Cardinal.aleph0 := by
    have h1 : Cardinal.mk ι =
        Cardinal.mk (⋃ q : Quotient s, {i : ι | Quotient.mk s i = q}) := by
      rw [← huniv, Cardinal.mk_univ]
    rw [h1]
    refine Cardinal.mk_iUnion_le_sum_mk.trans ?_
    refine (Cardinal.sum_le_sum _ (fun _ ↦ Cardinal.aleph0) fun q ↦ ?_).trans ?_
    · exact Cardinal.mk_le_aleph0_iff.mpr (hcq q)
    · rw [Cardinal.sum_const']
  -- so the quotient itself is continuum-sized
  have hQle : Cardinal.mk (Quotient s) ≤ Cardinal.continuum := by
    rw [← hcard]
    exact Cardinal.mk_le_of_surjective Quotient.mk_surjective
  have hQinf : Cardinal.aleph0 < Cardinal.mk (Quotient s) := by
    by_contra hcon
    have hcon' : Cardinal.mk (Quotient s) ≤ Cardinal.aleph0 := not_lt.mp hcon
    have hsmall : Cardinal.mk ι ≤ Cardinal.aleph0 := by
      refine hle.trans ?_
      calc Cardinal.mk (Quotient s) * Cardinal.aleph0
          ≤ Cardinal.aleph0 * Cardinal.aleph0 := by gcongr
        _ = Cardinal.aleph0 := Cardinal.aleph0_mul_aleph0
    rw [hcard] at hsmall
    exact absurd (hsmall.trans_lt Cardinal.aleph0_lt_continuum) (lt_irrefl _)
  have hQeq : Cardinal.mk (Quotient s) = Cardinal.continuum := by
    refine le_antisymm hQle ?_
    have hmax : Cardinal.mk (Quotient s) * Cardinal.aleph0 =
        Cardinal.mk (Quotient s) := by
      rw [Cardinal.mul_eq_max hQinf.le le_rfl, max_eq_left hQinf.le]
    rw [← hcard]
    exact hle.trans hmax.le
  -- a transversal of the classes is the family we want
  refine ⟨Set.range (Quotient.out : Quotient s → ι), ?_, ?_, ?_⟩
  · rw [Cardinal.mk_range_eq _ Quotient.out_injective]
    exact hQeq
  · rintro i -
    exact product_fg_not_isOperatorMF N i
  · rintro i ⟨q, rfl⟩ j ⟨p, rfl⟩ he
    have hq : Quotient.mk s q.out = Quotient.mk s p.out := Quotient.sound he
    rw [Quotient.out_eq, Quotient.out_eq] at hq
    rw [hq]

end ContinuumMultiplicity
end GroupApproximation
