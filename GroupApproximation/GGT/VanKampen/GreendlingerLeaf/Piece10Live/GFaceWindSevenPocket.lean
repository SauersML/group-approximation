import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindSixIter
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: part (d) without `PosStep`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-64.

Route.  Drop the sign condition: from any reached state, excision steps can be iterated all
the way to the empty walk.  While the walk repeats a vertex, `gfaceWindFive_step` gives a
step; once it repeats none, it is a simple closed walk (`gfaceWindSix_simple`) and excising
the whole walk as an inner stretch is a step.  Each step shortens the walk
(`gfaceWind_step_inv`), and at the empty walk `g = 0` (`gfaceWindSix_nil`).
This is `gfaceWindSeven_toNil`.

* `gfaceWindSeven_pocket` (proved, **no hypothesis**): the exact conclusion of
  `gfaceWindSix_pocket`, witnessed by the empty terminal state.

**LOUD: `gfaceWindSix_PosStep` is not needed for `gfaceWindSix_pocket`.**  The conclusion of
part (d) as stated there is too weak to carry the winding choice: it is met by the empty walk
with `g = 0`, which never satisfies the face-set clauses (the pocket is pinched, so the chosen
`F'` must be nonempty).  Closing `gfaceWindSix_Statement` needs a strictly stronger terminal
statement; the terminal-state strategy is FALSE as a complete strategy (gl-p10-61: 2770 of
14416, 4084 of 20984, 0 of 7258 no-loop decompositions).

## Truth check

Pure bookkeeping on proved lemmas; no new mathematical input.  (The empty walk is reached
because every nonempty walk has a step and steps shorten the walk.)

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **Excising down to the empty walk**: from any reached state an excision sequence reaches
the empty walk, where `g = 0`. -/
theorem gfaceWindSeven_toNil {M : CombMap.{v}} (hM : M.IsPlanar) {C : List M.Dart}
    {F : Finset M.Face} {o : M.Face} (hC : C.Nodup)
    (hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ C)
    (hch : C.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hbal : gfaceWindSix_Bal M C) (ho : o ∉ F) :
    ∀ (n : ℕ) (c : List M.Dart) (g : M.Face → ℤ), c.length = n →
      Relation.ReflTransGen (gfaceWind_Step M o) (C, gfaceWind_ind F) (c, g) →
        ∃ g' : M.Face → ℤ, Relation.ReflTransGen (gfaceWind_Step M o) (c, g) ([], g') ∧
          ∀ f, g' f = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c g hn hr
    have hinv : gfaceWind_Inv M C o c g :=
      gfaceWindSix_inv_rt (s := (C, gfaceWind_ind F)) (t := (c, g)) hM hC hr
        (gfaceWind_inv_start hS hch ho)
    rcases eq_or_ne c [] with hc0 | hne
    · subst hc0
      exact ⟨g, Relation.ReflTransGen.refl,
        gfaceWindSix_nil (M.connected_of_planar hM) hinv.2.2.1 hinv.2.2.2⟩
    · have hsub : ∀ x ∈ c, x ∈ C := by
        intro x hx
        have hx' : x ∈ C.filter (gfaceWind_mem c) := by
          rw [hinv.1]
          exact hx
        exact (List.mem_filter.mp hx').1
      have hal : ∀ x ∈ c, M.alpha x ∉ c := fun x hx hax =>
        ((hS x).mpr (hsub x hx)).2 ((hS _).mpr (hsub _ hax)).1
      have hex : ∃ t : List M.Dart × (M.Face → ℤ), gfaceWind_Step M o (c, g) t := by
        by_cases hnd : (c.map M.vertexOf).Nodup
        · have hbc : gfaceWindSix_Bal M c :=
            gfaceWindSix_bal_reach (s := (C, gfaceWind_ind F)) (t := (c, g)) hr hbal
          have hw := gfaceWindSix_simple hne hinv.2.1 hbc hnd hal
          have hseg : c = [] ++ c ++ [] := by simp
          exact ⟨([] ++ [], fun f => g f - gfaceWind_wind M o c f), [], c, [], hseg,
            Or.inl ⟨hw, rfl, rfl⟩⟩
        · exact gfaceWindFive_step o g hinv.2.1 hal hnd
      obtain ⟨⟨c1, g1⟩, hst⟩ := hex
      have hlt : c1.length < c.length :=
        (gfaceWind_step_inv (s := (c, g)) (t := (c1, g1)) hM hC hinv hst).2
      obtain ⟨g', hr', hg'⟩ := ih c1.length (by omega) c1 g1 rfl (hr.tail hst)
      exact ⟨g', Relation.ReflTransGen.head hst hr', hg'⟩

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Part (d) on a pinched pocket, unconditionally**: the conclusion of `gfaceWindSix_pocket`
without the hypothesis `gfaceWindSix_PosStep`, witnessed by the empty terminal state. -/
theorem gfaceWindSeven_pocket (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hpinch : ¬Unpinched X.toCombMap K.faces) :
    ∃ (c : List X.toCombMap.Dart) (g : X.toCombMap.Face → ℤ),
      Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
        (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) ∧
      (c.map X.toCombMap.vertexOf).Nodup ∧ (∀ f, g f = 0 ∨ g f = 1) ∧
      (c = [] ∨ (IsSimpleClosedWalk X.toCombMap c ∧
        ∀ f, g f = gfaceWind_ind (sideFaces X.toCombMap c) f)) := by
  have hc := K.boundary.cycle_mem_iff
  have hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart X.toCombMap K.faces d ↔
      d ∈ K.boundary.cycle :=
    fun d => (hc d).symm
  have hbal : gfaceWindSix_Bal X.toCombMap K.boundary.cycle :=
    (gfaceWindSix_bal_iff K.boundary.cycle_nonempty hK.1).mpr hK.2
  obtain ⟨⟨c1, g1⟩, hst, -, -⟩ := gfaceWindFive_pocket_step K hK hpinch
  obtain ⟨g, hr, hg⟩ := gfaceWindSeven_toNil X.planar K.boundary.cycle_nodup hS hK.1 hbal
    K.outerFace_not_mem c1.length c1 g1 rfl (Relation.ReflTransGen.single hst)
  have hnd : (([] : List X.toCombMap.Dart).map X.toCombMap.vertexOf).Nodup := by simp
  exact ⟨[], g, Relation.TransGen.head' hst hr, hnd, fun f => Or.inl (hg f), Or.inl rfl⟩

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSeven_toNil
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSeven_pocket
