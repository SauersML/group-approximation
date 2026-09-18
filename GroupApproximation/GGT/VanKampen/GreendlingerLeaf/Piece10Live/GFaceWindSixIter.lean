import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindSixBal
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindSixCore
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindFiveStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: iterating excision steps to a vertex-simple state

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-61.

Route.  Part (d) of the winding choice asks for an excision sequence ending in a `0/1`-valued
`g`.  Iterate excision steps by well-founded recursion on the walk length (each step shortens
the walk, `gfaceWind_step_inv`) until the walk repeats no vertex (`gfaceWindSix_iter`).  At such
a terminal state the walk is empty or a simple closed walk: it is closed by balance
(`gfaceWindSix_bal_reach`), repeats no vertex, and reverses no dart since it is a sub-list of the
pocket walk.  If `g ≥ 0` there, then `g` is `0` or the indicator of the side of the walk
(`gfaceWindSix_terminal`, from `gfaceWindSix_zero_one`), so `0/1`-valued.

The one missing ingredient is isolated as `gfaceWindSix_PosStep`: from a reached pinched state
with `g ≥ 0` some excision step keeps `g ≥ 0`.  (`gfaceWindFive_step` gives a step, but the
innermost lobe of `ClosedWalkInnermostLobe` does not control the sign of the new `g`.)

* `gfaceWindSix_inv_rt` (proved): the invariant along reflexive excision sequences.
* `gfaceWindSix_PosStep` (hypothesis, see the truth check).
* `gfaceWindSix_iter` (proved from `PosStep`): a vertex-simple state with `g ≥ 0` is reached.
* `gfaceWindSix_terminal` (proved): such a state is empty with `g = 0`, or simple with `g` the
  side indicator.
* `gfaceWindSix_pocket` (proved from `PosStep`): on a pinched pocket, a nonempty excision
  sequence to a vertex-simple `0/1`-valued state.

**LOUD: this is part (d) only.**  The reached state of `gfaceWindSix_pocket` need NOT satisfy
the face-set clauses: as a complete strategy the terminal state is FALSE (truth check).

## Truth check

Scratchpad `gl-p10-61/six.py`, on the Lean-faithful models of `gl-p10-49/gface.py` and the
integer reach of `gl-p10-55/wind.py`.  `PosStep`: 0 failures (random seed 1: 819169 states,
seed 3: 1042430, witness seed 2: 1258036).  Terminal vertex-simple states with `g ≥ 0` are
`0/1`-valued: 0 failures.  **FALSE as a complete strategy**: a terminal state satisfies the
face-set clauses only in 2770 of 14416 (seed 1), 4084 of 20984 (seed 3), 0 of 7258 (witness)
no-loop decompositions.  The searches do not model least area or labels.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **The invariant along reflexive excision sequences.** -/
theorem gfaceWindSix_inv_rt {M : CombMap.{v}} (hM : M.IsPlanar) {C : List M.Dart}
    (hC : C.Nodup) {o : M.Face} {s t : List M.Dart × (M.Face → ℤ)}
    (h : Relation.ReflTransGen (gfaceWind_Step M o) s t) (hs : gfaceWind_Inv M C o s.1 s.2) :
    gfaceWind_Inv M C o t.1 t.2 := by
  induction h with
  | refl => exact hs
  | tail _ hst ih => exact (gfaceWind_step_inv hM hC ih hst).1

/-- **A sign-keeping excision step** (hypothesis; true in all models, see the module
docstring).  From a state reached from a closed duplicate-free walk `C` bounding `F`, with
`g ≥ 0` and a repeated vertex, some excision step keeps `g ≥ 0`. -/
def gfaceWindSix_PosStep : Prop :=
  ∀ (M : CombMap.{v}), M.IsPlanar → ∀ (C : List M.Dart) (F : Finset M.Face) (o : M.Face),
    C.Nodup → (∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ C) →
    C.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) → gfaceWindSix_Bal M C →
    o ∉ F → ∀ (c : List M.Dart) (g : M.Face → ℤ),
      Relation.ReflTransGen (gfaceWind_Step M o) (C, gfaceWind_ind F) (c, g) →
      (∀ f, 0 ≤ g f) → ¬ (c.map M.vertexOf).Nodup →
        ∃ t : List M.Dart × (M.Face → ℤ), gfaceWind_Step M o (c, g) t ∧ ∀ f, 0 ≤ t.2 f

/-- **Iterating sign-keeping steps** by well-founded recursion on the walk length reaches a
state whose walk repeats no vertex, with `g ≥ 0`. -/
theorem gfaceWindSix_iter (hP : gfaceWindSix_PosStep.{v}) {M : CombMap.{v}} (hM : M.IsPlanar)
    {C : List M.Dart} {F : Finset M.Face} {o : M.Face} (hC : C.Nodup)
    (hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ C)
    (hch : C.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hbal : gfaceWindSix_Bal M C) (ho : o ∉ F) :
    ∀ (n : ℕ) (c : List M.Dart) (g : M.Face → ℤ), c.length = n →
      Relation.ReflTransGen (gfaceWind_Step M o) (C, gfaceWind_ind F) (c, g) →
      (∀ f, 0 ≤ g f) →
        ∃ (c' : List M.Dart) (g' : M.Face → ℤ),
          Relation.ReflTransGen (gfaceWind_Step M o) (c, g) (c', g') ∧
          (c'.map M.vertexOf).Nodup ∧ ∀ f, 0 ≤ g' f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c g hn hr hpos
    by_cases hnd : (c.map M.vertexOf).Nodup
    · exact ⟨c, g, Relation.ReflTransGen.refl, hnd, hpos⟩
    · obtain ⟨⟨c1, g1⟩, hst, hpos1⟩ := hP M hM C F o hC hS hch hbal ho c g hr hpos hnd
      have hinv : gfaceWind_Inv M C o c g :=
        gfaceWindSix_inv_rt (s := (C, gfaceWind_ind F)) (t := (c, g)) hM hC hr
          (gfaceWind_inv_start hS hch ho)
      have hlt : c1.length < c.length :=
        (gfaceWind_step_inv (s := (c, g)) (t := (c1, g1)) hM hC hinv hst).2
      obtain ⟨c', g', hr', hnd', hpos'⟩ :=
        ih c1.length (by omega) c1 g1 rfl (hr.tail hst) hpos1
      exact ⟨c', g', Relation.ReflTransGen.head hst hr', hnd', hpos'⟩

/-- **Terminal states**: a reached state whose walk repeats no vertex, with `g ≥ 0`, has either
the empty walk and `g = 0`, or a simple closed walk with `g` the indicator of its side. -/
theorem gfaceWindSix_terminal {M : CombMap.{v}} (hM : M.IsPlanar) {C : List M.Dart}
    {F : Finset M.Face} {o : M.Face} (hC : C.Nodup)
    (hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ C)
    (hch : C.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hbal : gfaceWindSix_Bal M C) (ho : o ∉ F) {c : List M.Dart} {g : M.Face → ℤ}
    (hr : Relation.ReflTransGen (gfaceWind_Step M o) (C, gfaceWind_ind F) (c, g))
    (hnd : (c.map M.vertexOf).Nodup) (hpos : ∀ f, 0 ≤ g f) :
    (c = [] ∧ ∀ f, g f = 0) ∨
      (IsSimpleClosedWalk M c ∧ ∀ f, g f = gfaceWind_ind (sideFaces M c) f) := by
  have hinv : gfaceWind_Inv M C o c g :=
    gfaceWindSix_inv_rt (s := (C, gfaceWind_ind F)) (t := (c, g)) hM hC hr
      (gfaceWind_inv_start hS hch ho)
  obtain ⟨hfil, hchc, hcob, hog⟩ := hinv
  have hsub : ∀ x ∈ c, x ∈ C := by
    intro x hx
    have hx' : x ∈ C.filter (gfaceWind_mem c) := by
      rw [hfil]
      exact hx
    exact (List.mem_filter.mp hx').1
  have hal : ∀ x ∈ c, M.alpha x ∉ c := fun x hx hax =>
    ((hS x).mpr (hsub x hx)).2 ((hS _).mpr (hsub _ hax)).1
  rcases eq_or_ne c [] with hc0 | hne
  · subst hc0
    exact Or.inl ⟨rfl, gfaceWindSix_nil (M.connected_of_planar hM) hcob hog⟩
  · have hbc : gfaceWindSix_Bal M c :=
      gfaceWindSix_bal_reach (s := (C, gfaceWind_ind F)) (t := (c, g)) hr hbal
    have hw := gfaceWindSix_simple hne hchc hbc hnd hal
    exact Or.inr ⟨hw, (gfaceWindSix_zero_one hM hw hcob hog hpos).2⟩

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Part (d) on a pinched pocket, from `PosStep`**: a nonempty excision sequence from the
start state to a state whose walk repeats no vertex and whose `g` is `0/1`-valued, namely `0`
on the empty walk or the side indicator of a simple closed walk. -/
theorem gfaceWindSix_pocket (hP : gfaceWindSix_PosStep.{v}) (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (hpinch : ¬Unpinched X.toCombMap K.faces) :
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
  have hpos0 : ∀ f, 0 ≤ gfaceWind_ind K.faces f := by
    intro f
    rcases gfaceWindSix_ind01 K.faces f with h | h <;> linarith
  obtain ⟨⟨c1, g1⟩, hst, hpos1⟩ := hP X.toCombMap X.planar K.boundary.cycle K.faces
    X.outerFace K.boundary.cycle_nodup hS hK.1 hbal K.outerFace_not_mem K.boundary.cycle
    (gfaceWind_ind K.faces) Relation.ReflTransGen.refl hpos0 (gfaceWindFive_not_nodup K hpinch)
  obtain ⟨c, g, hr, hnd, hpos⟩ := gfaceWindSix_iter hP X.planar K.boundary.cycle_nodup hS hK.1
    hbal K.outerFace_not_mem c1.length c1 g1 rfl (Relation.ReflTransGen.single hst) hpos1
  have hr' : Relation.ReflTransGen (gfaceWind_Step X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) :=
    Relation.ReflTransGen.head hst hr
  have hT : Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) :=
    Relation.TransGen.head' hst hr
  rcases gfaceWindSix_terminal X.planar K.boundary.cycle_nodup hS hK.1 hbal
      K.outerFace_not_mem hr' hnd hpos with ⟨h0, hg⟩ | ⟨hw, hg⟩
  · exact ⟨c, g, hT, hnd, fun f => Or.inl (hg f), Or.inl h0⟩
  · refine ⟨c, g, hT, hnd, fun f => ?_, Or.inr ⟨hw, hg⟩⟩
    rw [hg f]
    exact gfaceWindSix_ind01 _ f

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_inv_rt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_PosStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_iter
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_terminal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_pocket
