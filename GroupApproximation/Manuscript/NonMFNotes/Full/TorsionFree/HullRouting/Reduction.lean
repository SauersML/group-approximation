import GroupApproximation.GGT.HullSC
import GroupApproximation.GGT.ElementaryOsinNormalClosed
import GroupApproximation.Manuscript.NonMF.Saturation
import GroupApproximation.Manuscript.NonMF.HullBallForm
import GroupApproximation.Meta.AxiomGuard

/-!
# Routing an infinite normal subgroup through Hull's Theorem 7.1

`non_mf_group_notes.tex`, Theorem `thm:torsionfree`, l.2786-2796:

> Put `N = ⟨⟨S'⟩⟩_{G_0}`. This subgroup is infinite and normal, so s-normal. By Osin's lemma,
> `N` acts non-elementarily [Osin, Lemma 7.1]. The finite radical of the torsion-free group
> `G_0` is trivial, so `N` is suitable. Apply Theorem 7.1 of [Hull] with the elements `t_i`
> equal to a finite generating set of `G_0` and with an injectivity radius containing a fixed
> nonidentity element of `S'` [...]. The group `G` is torsion-free by Theorem 7.1(e) [...].
> Condition (c) gives that the image of `N` equals `G`.

This module proves every step of that paragraph except the existence of Hull's quotient itself:

* `suitable_of_infinite_normal`: an infinite normal subgroup of a torsion-free group is
  suitable for Hull's alphabet. s-normality is `TorsionFree.isSNormal_of_torsionFree`, Osin's
  Lemma 7.1 is the closed `GGT.Elementary.osinNonElementary_of_torsionFree_normal_closed`, and
  the finite-radical clause is `TorsionFree.suitable_of_torsionFree`.
* `exists_fin_generating_family`: a finitely generated group has a finite generating family
  `t₁, …, t_m`.
* `exists_routingParameters`: Hull's alphabet, the generating family and an injectivity radius
  whose ball contains a prescribed finite set.
* `routedQuotient_of_hullTower`: a Hull tower (`HullSC.HullTower`, the output of Hull's
  Theorem 7.1) for those parameters gives the routed quotient: clause (b) gives injectivity on
  `F`, clause (c) with the generating family gives `N.map q = ⊤`, and clause (e) gives
  torsion-freeness.

The tower is a datum here, not a quantified statement. The existence of the tower at every
acylindrically hyperbolic group is `HullSC.hullTowerStatementGeneral_of_leastAreaLeaves`, over
the least-area Greendlinger leaf.
-/

namespace GroupApproximation.Full.NN07d

universe u

open GroupApproximation.HullGeometry

/-- **"This subgroup is infinite and normal, so s-normal. By Osin's lemma, `N` acts
non-elementarily. The finite radical of the torsion-free group `G_0` is trivial, so `N` is
suitable."** (`thm:torsionfree`, `non_mf_group_notes.tex` l.2786-2789.) -/
theorem suitable_of_infinite_normal {G : Type u} [Group G]
    (A : Manuscript.NonMF.TorsionFree.HullGeneratingSet G) (hG : IsPowerTorsionFree G)
    (N : Subgroup G) [N.Normal] (hN : (N : Set G).Infinite) :
    Manuscript.NonMF.TorsionFree.Suitable A.alphabet N := by
  have hbot : N ≠ ⊥ := by
    intro h
    apply hN
    rw [h, Subgroup.coe_bot]
    exact Set.finite_singleton 1
  exact Manuscript.NonMF.TorsionFree.suitable_of_torsionFree hG
    (GGT.Elementary.osinNonElementary_of_torsionFree_normal_closed A hG N
      (Manuscript.NonMF.TorsionFree.isSNormal_of_torsionFree hG N hbot))

/-- **"the elements `t_i` equal to a finite generating set of `G_0`"** (`thm:torsionfree`,
`non_mf_group_notes.tex` l.2790): a finitely generated group has a finite generating family. -/
theorem exists_fin_generating_family (G : Type u) [Group G] [h : Group.FG G] :
    ∃ (m : ℕ) (t : Fin m → G), Subgroup.closure (Set.range t) = ⊤ := by
  obtain ⟨S, hS⟩ := h.out
  refine ⟨S.card, fun i => ((S.equivFin.symm i : S) : G), ?_⟩
  have hrange : Set.range (fun i : Fin S.card => ((S.equivFin.symm i : S) : G)) =
      (S : Set G) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.mem_coe.mpr (S.equivFin.symm i).2
    · intro hx
      refine ⟨S.equivFin ⟨x, Finset.mem_coe.mp hx⟩, ?_⟩
      exact congrArg Subtype.val
        (Equiv.symm_apply_apply S.equivFin ⟨x, Finset.mem_coe.mp hx⟩)
  rw [hrange]
  exact hS

/-- **The parameters of the application of Hull's Theorem 7.1** (`thm:torsionfree`,
`non_mf_group_notes.tex` l.2789-2792): Hull's alphabet `A`, for which `N` is suitable, a finite
generating family `t`, and a radius `R` whose ball in `Γ(G,A)` contains `F`. -/
theorem exists_routingParameters {G : Type u} [Group G] [Group.FG G]
    [Manuscript.NonMF.TorsionFree.IsAcylindricallyHyperbolic G]
    (hG : IsPowerTorsionFree G) (N : Subgroup G) [N.Normal] (hN : (N : Set G).Infinite)
    {F : Set G} (hF : F.Finite) :
    ∃ (A : Manuscript.NonMF.TorsionFree.HullGeneratingSet G) (m : ℕ) (t : Fin m → G) (R : ℕ),
      Manuscript.NonMF.TorsionFree.Suitable A.alphabet N ∧
        Subgroup.closure (Set.range t) = ⊤ ∧
          F ⊆ Manuscript.NonMF.TorsionFree.cayleyBall A.alphabet R := by
  obtain ⟨A⟩ := Manuscript.NonMF.TorsionFree.exists_hullGeneratingSet G
  obtain ⟨m, t, htop⟩ := exists_fin_generating_family G
  obtain ⟨R, hR⟩ := Manuscript.NonMF.TorsionFree.exists_subset_cayleyBall A.alphabet hF
  exact ⟨A, m, t, R, suitable_of_infinite_normal A hG N hN, htop, hR⟩

/-- **The routed quotient from Hull's quotient** (`thm:torsionfree`, `non_mf_group_notes.tex`
l.2792-2796). A Hull tower for a generating family `t` and a radius whose ball contains `F`
gives a surjection `q` onto a torsion-free group with `q(N) = Q`, injective on `F`:

* Theorem 7.1(b), injectivity on the ball, restricts to `F`;
* Theorem 7.1(c), `q(tᵢ) ∈ q(N)`, gives `q(N) = Q` because the `tᵢ` generate;
* Theorem 7.1(e), lifting finite order with its order, gives torsion-freeness. -/
theorem routedQuotient_of_hullTower {G : Type} [Group G] (hG : IsPowerTorsionFree G)
    {A : Manuscript.NonMF.TorsionFree.HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} {m : ℕ} {t : Fin m → G}
    (htop : Subgroup.closure (Set.range t) = ⊤) {R : ℕ} {F : Set G}
    (hFR : F ⊆ Manuscript.NonMF.TorsionFree.cayleyBall A.alphabet R)
    (T : HullSC.HullTower A N S t R) :
    ∃ (Q : Type) (_ : Group Q) (q : G →* Q), Function.Surjective q ∧
      IsPowerTorsionFree Q ∧ N.map q = ⊤ ∧ Set.InjOn q F :=
  ⟨T.step.Q, T.step.group, T.step.q, T.step.surjective,
    Manuscript.NonMF.TorsionFree.torsionFree_of_finiteOrder_lift hG T.step.q
      T.step.finiteOrder_lift,
    Manuscript.NonMF.TorsionFree.map_eq_top_of_generators_mem T.step.q T.step.surjective
      htop T.mem_map,
    T.step.injOn.mono hFR⟩

end GroupApproximation.Full.NN07d

#audit_closed_axioms GroupApproximation.Full.NN07d.suitable_of_infinite_normal
#audit_closed_axioms GroupApproximation.Full.NN07d.exists_fin_generating_family
#audit_closed_axioms GroupApproximation.Full.NN07d.exists_routingParameters
#audit_closed_axioms GroupApproximation.Full.NN07d.routedQuotient_of_hullTower
