import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.FaceClassTools
import GroupApproximation.Meta.AxiomGuard

/-!
# Holding small faces of the contact map: face classes and components of a restriction

Let `N = PredicateRestriction.toCombMap M keep hkeep` be the first-return restriction of a map `M`
to an `α`-invariant set of darts.  For a dart `x` of `N`, `CompKeep hkeep x` is the set of ambient
darts of the component of `x` in `N`.

* `compKeep_alpha`: this set is `α`-invariant.
* `faceOf_eq_of_compKeep` (separation inside a component): when `M` is planar and `x′` lies in the
  component of `x`, a face-class path of `M` from `x` to `x′` that crosses only edges off the
  component of `x` gives `N.faceOf x = N.faceOf x′`.  The component is a connected restriction of
  `M`, so `IsRestriction.faceOf_eq_of_faceClass` applies to it.  Its faces are the faces of `N`
  through its darts (`restrict_facePerm_eq`, `Equiv.Perm.sameCycle_subtypePerm`).
* `faceClass_of_componentOf` (blocks): if no vertex of `M` at a dart of the component of `x` carries
  a dart of `K`, the darts of that component lie in one face class off `K`.  This is induction on
  adjacency in `N`: an `α` step crosses an edge off `K`, and a `σ` step of `N` stays at one vertex
  of `M` (`IsRestriction.vertexOf_eq_iff`), which is swept by `faceClass_of_sameCycle`.
* `not_compKeep_of_componentOf`: when `x₂` is off the component of `x₁`, no vertex of `M` at a dart
  of the component of `x₁` carries a dart of the component of `x₂`.  The retained darts at one
  vertex of `M` form one vertex of `N`, so they share a component.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces

universe u

section Components

variable {M : CombMap.{u}} {keep : M.Dart → Prop} (hkeep : ∀ d, keep (M.alpha d) ↔ keep d)

/-- The ambient darts of the component of a retained dart. -/
def CompKeep (x : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart) (z : M.Dart) :
    Prop :=
  ∃ h : keep z, (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf x ⟨z, h⟩

theorem keep_of_compKeep {x : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    {z : M.Dart} (h : CompKeep hkeep x z) : keep z := by
  obtain ⟨hk, _⟩ := h
  exact hk

theorem compKeep_alpha (x : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart)
    (z : M.Dart) : CompKeep hkeep x (M.alpha z) ↔ CompKeep hkeep x z := by
  constructor
  · rintro ⟨hz, hc⟩
    have hk : keep z := (hkeep z).mp hz
    exact ⟨hk,
      ((CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf_alpha x ⟨z, hk⟩).mp hc⟩
  · rintro ⟨hz, hc⟩
    exact ⟨(hkeep z).mpr hz,
      ((CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf_alpha x ⟨z, hz⟩).mpr hc⟩

theorem compKeep_self (x : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart) :
    CompKeep hkeep x x.1 :=
  ⟨x.2, (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf_self x⟩

theorem compKeep_congr {x x' : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    (h : (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf x x') (z : M.Dart) :
    CompKeep hkeep x z ↔ CompKeep hkeep x' z := by
  constructor
  · rintro ⟨hk, hc⟩
    exact ⟨hk, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hc⟩
  · rintro ⟨hk, hc⟩
    exact ⟨hk, Relation.EqvGen.trans _ _ _ h hc⟩

/-- Darts at one vertex of the restriction lie at one vertex of the ambient map. -/
theorem sameCycle_of_vertexOf_eq
    {a b : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    (h : (CombMap.PredicateRestriction.toCombMap M keep hkeep).vertexOf a =
      (CombMap.PredicateRestriction.toCombMap M keep hkeep).vertexOf b) :
    M.sigma.SameCycle a.1 b.1 :=
  (M.vertexOf_eq_iff a.1 b.1).mp
    (((CombMap.PredicateRestriction.isRestriction M keep hkeep).vertexOf_eq_iff a b).mp h)

/-- Retained darts at one vertex of the ambient map lie at one vertex of the restriction. -/
theorem vertexOf_eq_of_sameCycle
    {a b : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    (h : M.sigma.SameCycle a.1 b.1) :
    (CombMap.PredicateRestriction.toCombMap M keep hkeep).vertexOf a =
      (CombMap.PredicateRestriction.toCombMap M keep hkeep).vertexOf b :=
  ((CombMap.PredicateRestriction.isRestriction M keep hkeep).vertexOf_eq_iff a b).mpr
    ((M.vertexOf_eq_iff a.1 b.1).mpr h)

/-- Retained darts at one vertex of the ambient map lie in one component of the restriction. -/
theorem componentOf_of_ambient_sameCycle
    {a b : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    (h : M.sigma.SameCycle a.1 b.1) :
    (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf a b :=
  componentOf_of_sameCycle (CombMap.PredicateRestriction.toCombMap M keep hkeep)
    (((CombMap.PredicateRestriction.toCombMap M keep hkeep).vertexOf_eq_iff a b).mp
      (vertexOf_eq_of_sameCycle hkeep h))

/-- **Separation inside a component**, off the edges of the component. -/
theorem faceOf_eq_of_compKeep (hM : M.IsPlanar)
    {d d' : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    (hcomp : (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf d d')
    (hp : Relation.EqvGen (CombMap.FaceClassStep M (CompKeep hkeep d)) d.1 d'.1) :
    (CombMap.PredicateRestriction.toCombMap M keep hkeep).faceOf d =
      (CombMap.PredicateRestriction.toCombMap M keep hkeep).faceOf d' := by
  let N := CombMap.PredicateRestriction.toCombMap M keep hkeep
  have hNK : N.IsRestriction (N.component d)
      (Function.Embedding.subtype (N.componentOf d)) :=
    N.restrict_isRestriction (N.componentOf d) (N.componentOf_alpha d) (N.componentOf_sigma d)
  have hMK := (CombMap.PredicateRestriction.isRestriction M keep hkeep).trans hNK
  have hmono : CombMap.FaceClassStep M (CompKeep hkeep d) ≤
      CombMap.FaceClassStep M (· ∈ Set.range ((Function.Embedding.subtype (N.componentOf d)).trans
        (Function.Embedding.subtype keep))) := by
    intro x y hxy
    rcases hxy with h | ⟨hnk, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, h⟩
      rintro ⟨z, rfl⟩
      exact hnk ⟨z.1.2, z.2⟩
  have hface := hMK.faceOf_eq_of_faceClass hM (N.component_connected d)
    (d := ⟨d, N.componentOf_self d⟩) (d' := ⟨d', hcomp⟩) (Relation.EqvGen.mono hmono _ _ hp)
  have hsc := ((N.component d).faceOf_eq_iff _ _).mp hface
  have hperm : (N.component d).facePerm =
      N.facePerm.subtypePerm (N.facePerm_invariant (N.componentOf d) (N.componentOf_alpha d)
        (N.componentOf_sigma d)) :=
    N.restrict_facePerm_eq (N.componentOf d) (N.componentOf_alpha d) (N.componentOf_sigma d)
  rw [hperm] at hsc
  exact (N.faceOf_eq_iff d d').mpr (Equiv.Perm.sameCycle_subtypePerm.mp hsc)

/-- **Blocks**: a component whose ambient vertices avoid `K` lies in one face class off `K`. -/
theorem faceClass_of_componentOf {K : M.Dart → Prop}
    (x : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart)
    (hK : ∀ w, (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf x w →
      ∀ z, M.sigma.SameCycle w.1 z → ¬ K z)
    {w : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    (hw : (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf x w) :
    Relation.EqvGen (CombMap.FaceClassStep M K) x.1 w.1 := by
  have key : ∀ a b, Relation.EqvGen (CombMap.PredicateRestriction.toCombMap M keep hkeep).Adjacent
      a b → (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf x a →
        Relation.EqvGen (CombMap.FaceClassStep M K) a.1 b.1 := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      intro ha
      rcases hab with rfl | rfl
      · exact faceClass_alpha (hK a ha a.1 (Equiv.Perm.SameCycle.refl _ _))
      · exact faceClass_of_sameCycle (hK a ha) (sameCycle_of_vertexOf_eq hkeep
          ((CombMap.PredicateRestriction.toCombMap M keep hkeep).vertexOf_sigma a).symm)
    | refl a =>
      intro _
      exact Relation.EqvGen.refl _
    | symm a b hab ih =>
      intro hb
      exact Relation.EqvGen.symm _ _
        (ih (Relation.EqvGen.trans _ _ _ hb (Relation.EqvGen.symm _ _ hab)))
    | trans a b c hab _ ih₁ ih₂ =>
      intro ha
      exact Relation.EqvGen.trans _ _ _ (ih₁ ha) (ih₂ (Relation.EqvGen.trans _ _ _ ha hab))
  exact key x w hw (Relation.EqvGen.refl _)

/-- **Vertices of one component carry no dart of another component.** -/
theorem not_compKeep_of_componentOf
    {x₁ x₂ : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    (h12 : ¬ (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf x₁ x₂)
    {w : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    (hw : (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf x₁ w)
    {z : M.Dart} (hz : M.sigma.SameCycle w.1 z) : ¬ CompKeep hkeep x₂ z := by
  rintro ⟨hk, hc⟩
  have hv : (CombMap.PredicateRestriction.toCombMap M keep hkeep).componentOf w ⟨z, hk⟩ :=
    componentOf_of_ambient_sameCycle hkeep (a := w) (b := ⟨z, hk⟩) hz
  exact h12 (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hw hv)
    (Relation.EqvGen.symm _ _ hc))

end Components

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.faceOf_eq_of_compKeep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.faceClass_of_componentOf
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.not_compKeep_of_componentOf
