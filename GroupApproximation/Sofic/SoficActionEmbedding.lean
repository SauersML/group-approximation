import GroupApproximation.Sofic.SoficAction

/-!
# Soficity of an action passes to equivariantly embedded subsystems

`SoficAction.restrict` shrinks the *window* of a model, and
`IsSoficAction.compHom` shrinks the *acting group*.  Missing was the third
direction: shrinking the *space*.

A sofic action model is a finite set of model points, a large "good" subset, and
for each good point an injective chart from the tested window of the space into
a finite chart set, intertwining the tested translations.  Nothing in that data
refers to the space except through the window and the charts.  So if `X` sits
inside `Y` by an injective equivariant map, a model for `Y` is already a model
for `X`: test the window's image, and precompose the charts with the embedding.
Injectivity of the composite is injectivity of the embedding composed with
injectivity of the chart, and equivariance of the composite is equivariance of
the chart composed with equivariance of the embedding.

That is `IsSoficAction.of_equivariant_injective`, and it is exactly the
principle the ascending-HNN descent needs: a sofic coset action of the ambient
group restricts to a sofic coset action of the compressed subgroup, because the
compressed coset space embeds equivariantly as one orbit.

Both spaces must live in the same universe, because a model's site and chart
types are built in the universe of the space it models.  That is not a
restriction in practice: the consumer embeds one coset space of `G` into
another.

The proof does no analysis and no approximation: it rebuilds the same model with
a composed chart, so the multiplicativity error and the good-set density are
inherited unchanged.  In particular nothing here is specific to soficity of
*groups*; it is a statement about the shape of the model.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G] {X Y : Type v}

/-- **Soficity passes to an equivariantly embedded space.**

If `ι : X → Y` is injective and equivariant and the action on `Y` is sofic, then
the action on `X` is sofic.  The model for `X` is the model for `Y` on the
translated window, with each chart precomposed by `ι`. -/
theorem IsSoficAction.of_equivariant_injective [MulAction G X] [MulAction G Y]
    (ι : X → Y) (hinj : Function.Injective ι)
    (hequiv : ∀ (g : G) (x : X), ι (g • x) = g • ι x)
    (hY : IsSoficAction G Y) : IsSoficAction G X := by
  classical
  intro F E ε hε
  obtain ⟨M⟩ := hY F (E.image ι) ε hε
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
    chart := fun s x => M.chart s (ι x)
    chart_inj := ?_
    chart_equivariant := ?_ }⟩
  · intro s hs x hx y hy hxy
    exact hinj (M.chart_inj s hs (ι x) (Finset.mem_image_of_mem _ hx)
      (ι y) (Finset.mem_image_of_mem _ hy) hxy)
  · intro g hg s hs hgs x hx hgx
    have hres := M.chart_equivariant g hg s hs hgs (ι x)
      (Finset.mem_image_of_mem _ hx)
      (by
        rw [← hequiv]
        exact Finset.mem_image_of_mem _ hgx)
    rw [hres, hequiv]

end GroupApproximation
