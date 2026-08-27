import GroupApproximation.Sofic.SoficActionExamples
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Approximating a coset action by larger quotients

**Proposition 30.3** of the dossier.  A transitive action `G ↷ G/H` is sofic as
soon as `H` can be approximated, on every finite set of membership tests, by
larger subgroups whose own coset actions are sofic.  This is the Chabauty-limit
step: only finitely many membership questions arise in any finite window, so a
subgroup agreeing with `H` on those questions already supplies a model.

Together with `isSoficAction_quotient_of_finiteIndex` (Lemma 30.2) this is the
mechanism that turns separability hypotheses on `H` into soficity of `G ↷ G/H`:
for a LERF group the approximating subgroups are of finite index.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- **Proposition 30.3.**  If every finite set of membership tests is resolved
correctly by some larger subgroup with a sofic coset action, then the coset
action of `H` is sofic.

The hypothesis says: for every finite `T ⊆ G` there is `K ⊇ H` which contains no
element of `T` outside `H`, and whose coset action is sofic.  Only two families
of tests are needed in a window — that distinct window points stay distinct, and
that the tested translations are recorded — and the first is what forces
elements outside `H` to stay outside `K`. -/
theorem isSoficAction_quotient_of_approximable (H : Subgroup G)
    (happrox : ∀ T : Finset G, ∃ K : Subgroup G, H ≤ K ∧
      (∀ g ∈ T, g ∉ H → g ∉ K) ∧ IsSoficAction G (G ⧸ K)) :
    IsSoficAction G (G ⧸ H) := by
  classical
  intro F E ε hε
  -- coset representatives for the window
  set σ : G ⧸ H → G := fun x => x.out with hσdef
  have hσ : ∀ x : G ⧸ H, (QuotientGroup.mk (σ x) : G ⧸ H) = x := fun x => x.out_eq
  -- the finite set of membership tests: separations between window points
  set T : Finset G := (E ×ˢ E).image (fun p => (σ p.1)⁻¹ * σ p.2) with hT
  obtain ⟨K, hHK, hsep, hK⟩ := happrox T
  -- the window transported to the larger quotient
  set q : G ⧸ H → G ⧸ K := fun x => QuotientGroup.mk (σ x) with hq
  have hqinj : ∀ x ∈ E, ∀ y ∈ E, q x = q y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    have hpair : ((x, y) : (G ⧸ H) × (G ⧸ H)) ∈ E ×ˢ E :=
      Finset.mem_product.mpr ⟨hx, hy⟩
    have hmem : (σ x)⁻¹ * σ y ∈ T := by
      rw [hT]
      exact Finset.mem_image_of_mem _ hpair
    have hnotH : (σ x)⁻¹ * σ y ∉ H := by
      intro hcon
      exact hne (by
        rw [← hσ x, ← hσ y]
        exact (QuotientGroup.eq (s := H)).mpr hcon)
    have hnotK : (σ x)⁻¹ * σ y ∉ K := hsep _ hmem hnotH
    exact hnotK ((QuotientGroup.eq (s := K)).mp hxy)
  have hqequiv : ∀ (g : G) (x : G ⧸ H), q (g • x) = g • q x := by
    intro g x
    have hH : (QuotientGroup.mk (σ (g • x)) : G ⧸ H)
        = QuotientGroup.mk (g * σ x) := by
      rw [hσ (g • x)]
      have hact : (QuotientGroup.mk (g * σ x) : G ⧸ H)
          = g • (QuotientGroup.mk (σ x) : G ⧸ H) := rfl
      rw [hact, hσ x]
    have hmemK : (σ (g • x))⁻¹ * (g * σ x) ∈ K :=
      hHK ((QuotientGroup.eq (s := H)).mp hH)
    have hKeq : (QuotientGroup.mk (σ (g • x)) : G ⧸ K)
        = QuotientGroup.mk (g * σ x) := (QuotientGroup.eq (s := K)).mpr hmemK
    show (QuotientGroup.mk (σ (g • x)) : G ⧸ K)
        = g • (QuotientGroup.mk (σ x) : G ⧸ K)
    have hact : (g • (QuotientGroup.mk (σ x) : G ⧸ K))
        = QuotientGroup.mk (g * σ x) := rfl
    rw [hact]
    exact hKeq

  -- a model for the larger quotient, transported back
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
    exact hqinj x hx y hy
      (M.chart_inj s hs (q x) (Finset.mem_image_of_mem _ hx) (q y)
        (Finset.mem_image_of_mem _ hy) hxy)
  · intro g hg s hs hgs x hx hgx
    have hres := M.chart_equivariant g hg s hs hgs (q x)
      (Finset.mem_image_of_mem _ hx)
      (by
        rw [← hqequiv]
        exact Finset.mem_image_of_mem _ hgx)
    rw [hres, hqequiv]


/-! ## Separable subgroups -/

/-- A finite intersection of finite-index subgroups has finite index. -/
theorem finiteIndex_finset_inf (s : Finset G) (Kf : G → Subgroup G)
    (h : ∀ g ∈ s, (Kf g).FiniteIndex) : (s.inf Kf).FiniteIndex := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.inf_empty]
      infer_instance
  | @insert a t ha ih =>
      rw [Finset.inf_insert]
      haveI : (Kf a).FiniteIndex := h a (Finset.mem_insert_self a t)
      haveI : (t.inf Kf).FiniteIndex :=
        ih fun g hg => h g (Finset.mem_insert_of_mem hg)
      infer_instance

/-- **Theorem 30.5, transitive case.**  If `H` is separable — every element
outside it is excluded by some finite-index subgroup containing it — then the
coset action `G ↷ G/H` is sofic.

For a LERF group every finitely generated subgroup is separable, so every
transitive action with finitely generated stabiliser is sofic. -/
theorem isSoficAction_quotient_of_separable (H : Subgroup G)
    (hsep : ∀ g : G, g ∉ H → ∃ K : Subgroup G, H ≤ K ∧ K.FiniteIndex ∧ g ∉ K) :
    IsSoficAction G (G ⧸ H) := by
  classical
  refine isSoficAction_quotient_of_approximable H ?_
  intro T
  -- the tested elements which actually lie outside `H`
  set T' : Finset G := T.filter (fun g => g ∉ H) with hT'
  choose Kf hKfle hKffi hKfnot using hsep
  -- a single finite-index subgroup excluding all of them at once
  refine ⟨T'.inf (fun g => if hg : g ∉ H then Kf g hg else ⊤), ?_, ?_, ?_⟩
  · refine Finset.le_inf fun g hg => ?_
    by_cases hgH : g ∉ H
    · rw [dif_pos hgH]; exact hKfle g hgH
    · rw [dif_neg hgH]; exact le_top
  · intro g hgT hgH hmem
    have hle : T'.inf (fun g => if hg : g ∉ H then Kf g hg else ⊤)
        ≤ (if hg : g ∉ H then Kf g hg else ⊤) :=
      Finset.inf_le (by rw [hT']; exact Finset.mem_filter.mpr ⟨hgT, hgH⟩)
    have := hle hmem
    rw [dif_pos hgH] at this
    exact hKfnot g hgH this
  · haveI : (T'.inf (fun g => if hg : g ∉ H then Kf g hg else ⊤)).FiniteIndex := by
      refine finiteIndex_finset_inf T' _ fun g _ => ?_
      by_cases hgH : g ∉ H
      · rw [dif_pos hgH]; exact hKffi g hgH
      · rw [dif_neg hgH]; infer_instance
    haveI : DecidableEq (G ⧸ (T'.inf (fun g => if hg : g ∉ H then Kf g hg else ⊤))) :=
      Classical.decEq _
    exact isSoficAction_quotient_of_finiteIndex _

end GroupApproximation
