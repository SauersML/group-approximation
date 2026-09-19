import GroupApproximation.Sofic.SoficActionOrbits

/-!
# Approximating a stabilizer from below

Section 30.5 approximates a subgroup by *larger* separable subgroups; for an
arbitrary stabilizer one also needs the opposite direction, since a general
subgroup is only an increasing union of finitely generated ones.  A finite
window of the coset space tests finitely many membership questions, and a
subgroup `K ≤ H` answering all of them positively already supplies the charts:
the representative map `G/H → G/K` is then injective and equivariant *on the
window*, which is all the model sees.

Consequently the finitely generated case of separability -- the actual LERF
hypothesis, and likewise the actual LERA hypothesis -- suffices: every action of
such a group on any set is sofic.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- **Approximation from below.**  If every finite set of membership tests is
answered by some smaller subgroup with a sofic coset action, then the coset
action of `H` is sofic. -/
theorem isSoficAction_quotient_of_approximable_below (H : Subgroup G)
    (happrox : ∀ T : Finset G, ∃ K : Subgroup G, K ≤ H ∧
      (∀ g ∈ T, g ∈ H → g ∈ K) ∧ IsSoficAction G (G ⧸ K)) :
    IsSoficAction G (G ⧸ H) := by
  classical
  intro F E ε hε
  set σ : G ⧸ H → G := fun x => x.out with hσdef
  have hσ : ∀ x : G ⧸ H, (QuotientGroup.mk (σ x) : G ⧸ H) = x := fun x => x.out_eq
  -- the tests: the translation cocycles of the window
  set T : Finset G := (F ×ˢ E).image
    (fun p : G × (G ⧸ H) => (σ (p.1⁻¹ • p.2))⁻¹ * (p.1⁻¹ * σ p.2)) with hT
  obtain ⟨K, hKH, hres, hK⟩ := happrox T
  set q : G ⧸ H → G ⧸ K := fun x => QuotientGroup.mk (σ x) with hq
  have hqinj : Function.Injective q := by
    intro x y hxy
    have hmem : (σ x)⁻¹ * σ y ∈ K := (QuotientGroup.eq (s := K)).mp hxy
    have : (QuotientGroup.mk (σ x) : G ⧸ H) = QuotientGroup.mk (σ y) :=
      (QuotientGroup.eq (s := H)).mpr (hKH hmem)
    rw [hσ x, hσ y] at this
    exact this
  -- the representative map is equivariant on the tested translations
  have hqequiv : ∀ g ∈ F, ∀ x ∈ E, q (g⁻¹ • x) = g⁻¹ • q x := by
    intro g hg x hx
    have hHmem : (σ (g⁻¹ • x))⁻¹ * (g⁻¹ * σ x) ∈ H := by
      refine (QuotientGroup.eq (s := H)).mp ?_
      rw [hσ (g⁻¹ • x)]
      show g⁻¹ • x = QuotientGroup.mk (g⁻¹ * σ x)
      have hact : (QuotientGroup.mk (g⁻¹ * σ x) : G ⧸ H)
          = g⁻¹ • (QuotientGroup.mk (σ x) : G ⧸ H) := rfl
      rw [hact, hσ x]
    have hTmem : (σ (g⁻¹ • x))⁻¹ * (g⁻¹ * σ x) ∈ T := by
      rw [hT]
      exact Finset.mem_image_of_mem _
        ((Finset.mem_product (p := ((g, x) : G × (G ⧸ H)))).mpr ⟨hg, hx⟩)
    have hKmem : (σ (g⁻¹ • x))⁻¹ * (g⁻¹ * σ x) ∈ K := hres _ hTmem hHmem
    show (QuotientGroup.mk (σ (g⁻¹ • x)) : G ⧸ K) = g⁻¹ • QuotientGroup.mk (σ x)
    have hact : (g⁻¹ • (QuotientGroup.mk (σ x) : G ⧸ K))
        = QuotientGroup.mk (g⁻¹ * σ x) := rfl
    rw [hact]
    exact (QuotientGroup.eq (s := K)).mpr hKmem
  obtain ⟨M⟩ := hK F (E.image q) ε hε
  refine ⟨{
    Site := M.Site
    siteFintype := M.siteFintype
    siteDecEq := M.siteDecEq
    siteNonempty := M.siteNonempty
    act := M.act
    act_one := M.act_one
    act_mul := M.act_mul
    good := M.good
    good_card := M.good_card
    Chart := M.Chart
    chartFintype := M.chartFintype
    chart := fun s x => M.chart s (q x)
    chart_inj := ?_
    chart_equivariant := ?_ }⟩
  · intro s hs x hx y hy hxy
    exact hqinj (M.chart_inj s hs (q x) (Finset.mem_image_of_mem _ hx) (q y)
      (Finset.mem_image_of_mem _ hy) hxy)
  · intro g hg s hs hgs x hx hgx
    have hshift : g⁻¹ • q x = q (g⁻¹ • x) := (hqequiv g hg x hx).symm
    have hres' := M.chart_equivariant g hg s hs hgs (q x)
      (Finset.mem_image_of_mem _ hx)
      (by
        rw [hshift]
        exact Finset.mem_image_of_mem _ hgx)
    rw [hres', hshift]

/-- Every subgroup is the increasing union of its finitely generated subgroups,
so soficity of the coset actions of the finitely generated ones suffices. -/
theorem isSoficAction_quotient_of_fg (H : Subgroup G)
    (hfg : ∀ K : Subgroup G, K.FG → K ≤ H → IsSoficAction G (G ⧸ K)) :
    IsSoficAction G (G ⧸ H) := by
  classical
  refine isSoficAction_quotient_of_approximable_below H fun T => ?_
  set S : Finset G := T.filter (fun g => g ∈ H) with hS
  refine ⟨Subgroup.closure (S : Set G), ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro g hg
    rw [hS, Finset.coe_filter] at hg
    exact hg.2
  · intro g hg hgH
    refine Subgroup.subset_closure ?_
    rw [hS, Finset.coe_filter]
    exact ⟨hg, hgH⟩
  · refine hfg _ ⟨S, rfl⟩ ?_
    rw [Subgroup.closure_le]
    intro g hg
    rw [hS, Finset.coe_filter] at hg
    exact hg.2

/-! ## LERF and LERA in their actual, finitely generated, form -/

/-- **Gao's theorem.**  If every *finitely generated* subgroup is separable,
every action of the group on any set is sofic. -/
theorem universallyActionSofic_of_fg_separable
    (hsep : ∀ K : Subgroup G, K.FG → ∀ g : G, g ∉ K →
      ∃ L : Subgroup G, K ≤ L ∧ L.FiniteIndex ∧ g ∉ L) :
    MarkedCompression.UniversallyActionSofic G := by
  intro Y _
  refine isSoficAction_of_stabilizers fun y => ?_
  refine isSoficAction_quotient_of_fg _ fun K hKfg _ => ?_
  exact isSoficAction_quotient_of_separable K (hsep K hKfg)

/-- **Theorem 30.7 with the dossier's hypothesis.**  If every finitely
generated subgroup is approximable by strongly co-amenable subgroups, every
action of the group is sofic. -/
theorem universallyActionSofic_of_fg_lera
    (hlera : ∀ K : Subgroup G, K.FG → ∀ T : Finset G,
      ∃ L : Subgroup G, K ≤ L ∧ (∀ g ∈ T, g ∉ K → g ∉ L) ∧
        StronglyCoAmenable L) :
    MarkedCompression.UniversallyActionSofic G := by
  intro Y _
  refine isSoficAction_of_stabilizers fun y => ?_
  refine isSoficAction_quotient_of_fg _ fun K hKfg _ => ?_
  refine isSoficAction_quotient_of_approximable K fun T => ?_
  obtain ⟨L, hKL, hsep, hL⟩ := hlera K hKfg T
  exact ⟨L, hKL, hsep, isSoficAction_quotient_of_stronglyCoAmenable L hL⟩

end GroupApproximation
