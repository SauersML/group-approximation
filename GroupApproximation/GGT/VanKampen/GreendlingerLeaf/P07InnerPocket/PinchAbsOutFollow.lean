import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsSubSub
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchFollowTurn
import GroupApproximation.GGT.VanKampen.BoundaryCycleFaceClass
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-74: a following outer cycle gives an edge connected outside

`pinchAbsOut_outside_of_follows`: for a noncrossing closed walk `w` of a planar map whose outer
cycle follows its boundary, `pinchAbsSub_Outside M w` holds (any two faces off `sideFaces M w`
are joined by faces off the side, consecutive ones sharing an edge).  No Euler hypothesis.

Plan.
* A face class step of the walk (`CombMap.FaceClassStep` with `walkKeep M w`) either stays in
  one face or crosses an edge off the walk; from a face off the side it therefore gives a chain of
  `pinchAbsSub_OutAdj` steps (`pinchAbsOut_chain`).
* Every face off the side is joined by such a chain to the face of a dart `y` with `α y ∈ w`, a
  dart of the outer cycle (`pinchAbsOut_exists`).  Otherwise the faces reached are closed under
  crossing every edge, hence (connectivity, `pinchAbsOut_const`) contain the face of a walk dart,
  which is on the side.
* All darts of a following boundary cycle lie in one face class of its cycle
  (`BoundaryCycle.eqvGen_of_mem_of_followsBoundary`); the edges of the outer cycle are those of
  `w` (`pinchAbsOut_mono`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse

/-- An edge with both faces off the side is an outside adjacency. -/
theorem pinchAbsOut_adj {M : CombMap.{v}} {w : List M.Dart} {d : M.Dart}
    (h₁ : M.faceOf d ∉ sideFaces M w) (h₂ : M.faceOf (M.alpha d) ∉ sideFaces M w) :
    pinchAbsSub_OutAdj M w (M.faceOf d) (M.faceOf (M.alpha d)) := by
  unfold pinchAbsSub_OutAdj
  exact ⟨h₁, h₂, d, rfl, rfl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_adj

/-- Outside adjacency is symmetric. -/
theorem pinchAbsOut_adj_symm {M : CombMap.{v}} {w : List M.Dart} {g h : M.Face}
    (hgh : pinchAbsSub_OutAdj M w g h) : pinchAbsSub_OutAdj M w h g := by
  unfold pinchAbsSub_OutAdj at hgh
  obtain ⟨hg, hh, d, rfl, rfl⟩ := hgh
  have e := pinchAbsOut_adj (w := w) hh (by rw [M.alpha_involutive d]; exact hg)
  rwa [M.alpha_involutive d] at e

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_adj_symm

/-- A chain of outside adjacencies can be reversed. -/
theorem pinchAbsOut_rev {M : CombMap.{v}} {w : List M.Dart} {g h : M.Face}
    (hgh : Relation.ReflTransGen (pinchAbsSub_OutAdj M w) g h) :
    Relation.ReflTransGen (pinchAbsSub_OutAdj M w) h g := by
  induction hgh with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (pinchAbsOut_adj_symm hbc) ih

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_rev

/-- A face class of the walk based off the side stays off the side. -/
theorem pinchAbsOut_off {M : CombMap.{v}} {w : List M.Dart} {x y : M.Dart}
    (hxy : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x y)
    (hx : M.faceOf x ∉ sideFaces M w) : M.faceOf y ∉ sideFaces M w :=
  (mem_sideOutside_iff M w _).mp
    (pinchFollow_faceClass_sideOutside ((mem_sideOutside_iff M w _).mpr hx) hxy)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_off

/-- **A face class of the walk based off the side is an outside chain.** -/
theorem pinchAbsOut_chain {M : CombMap.{v}} {w : List M.Dart} {x y : M.Dart}
    (hxy : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x y) :
    M.faceOf x ∉ sideFaces M w →
      Relation.ReflTransGen (pinchAbsSub_OutAdj M w) (M.faceOf x) (M.faceOf y) := by
  induction hxy with
  | rel a b hr =>
      intro ha
      rcases (show b = M.facePerm a ∨ (¬ walkKeep M w a ∧ b = M.alpha a) from hr) with
        rfl | ⟨hk, rfl⟩
      · exact (congrArg (Relation.ReflTransGen (pinchAbsSub_OutAdj M w) (M.faceOf a))
          (M.faceOf_facePerm a)).mpr .refl
      · have hrel : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) a (M.alpha a) :=
          .rel _ _ (Or.inr ⟨hk, rfl⟩)
        exact .single (pinchAbsOut_adj ha (pinchAbsOut_off hrel ha))
  | refl => intro _; exact .refl
  | symm _ _ hab ih =>
      intro hb
      exact pinchAbsOut_rev (ih (pinchAbsOut_off (.symm _ _ hab) hb))
  | trans _ _ _ hab _ ih₁ ih₂ =>
      intro ha
      exact (ih₁ ha).trans (ih₂ (pinchAbsOut_off hab ha))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_chain

/-- **A face property closed under crossing every edge is constant** on a connected map.
`σ d = facePerm (α d)`, so a rotation step stays in the face of `α d`. -/
theorem pinchAbsOut_const {M : CombMap.{v}} (hM : M.IsConnected) (P : M.Face → Prop)
    (hP : ∀ d, P (M.faceOf d) → P (M.faceOf (M.alpha d))) (x y : M.Dart)
    (hx : P (M.faceOf x)) : P (M.faceOf y) := by
  have hA : ∀ d, P (M.faceOf d) ↔ P (M.faceOf (M.alpha d)) := fun d =>
    ⟨hP d, fun h => by have e := hP _ h; rwa [M.alpha_involutive d] at e⟩
  have key : ∀ d e, M.Adjacent d e → (P (M.faceOf d) ↔ P (M.faceOf e)) := by
    intro d e hde
    rcases (show M.alpha d = e ∨ M.sigma d = e from hde) with rfl | rfl
    · exact hA d
    · have hs : M.sigma d = M.facePerm (M.alpha d) := by
        change M.sigma d = M.sigma (M.alpha (M.alpha d))
        rw [M.alpha_involutive d]
      rw [hs, M.faceOf_facePerm]
      exact hA d
  have hE : ∀ d e, Relation.EqvGen M.Adjacent d e → (P (M.faceOf d) ↔ P (M.faceOf e)) := by
    intro d e hde
    induction hde with
    | rel a b h => exact key a b h
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hE x y (hM x y)).mp hx

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_const

/-- **Every face off the side reaches the outer cycle.**  Some dart `y` with `α y ∈ w` has its
face off the side and joined to `g` by an outside chain. -/
theorem pinchAbsOut_exists {M : CombMap.{v}} {w : List M.Dart} (hM : M.IsConnected)
    (hne : w ≠ []) {g : M.Face} (hg : g ∉ sideFaces M w) :
    ∃ y, M.alpha y ∈ w ∧ M.faceOf y ∉ sideFaces M w ∧
      Relation.ReflTransGen (pinchAbsSub_OutAdj M w) g (M.faceOf y) := by
  by_contra hno
  obtain ⟨z, hz⟩ := Quotient.exists_rep g
  have hz' : M.faceOf z = g := hz
  subst hz'
  have hstep : ∀ d, (M.faceOf d ∉ sideFaces M w ∧
      Relation.ReflTransGen (pinchAbsSub_OutAdj M w) (M.faceOf z) (M.faceOf d)) →
      (M.faceOf (M.alpha d) ∉ sideFaces M w ∧
        Relation.ReflTransGen (pinchAbsSub_OutAdj M w) (M.faceOf z) (M.faceOf (M.alpha d))) := by
    rintro d ⟨hd, hr⟩
    have hk : ¬ walkKeep M w d := by
      intro hk
      rcases (show d ∈ w ∨ M.alpha d ∈ w from hk) with h | h
      · exact hd ((mem_sideFaces_iff M w d).mpr ⟨d, h, .refl _⟩)
      · exact hno ⟨d, h, hd, hr⟩
    have hrel : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) d (M.alpha d) :=
      .rel _ _ (Or.inr ⟨hk, rfl⟩)
    have hoff := pinchAbsOut_off hrel hd
    exact ⟨hoff, hr.tail (pinchAbsOut_adj hd hoff)⟩
  obtain ⟨d₀, hd₀⟩ := List.exists_mem_of_ne_nil w hne
  have h₀ : M.faceOf d₀ ∉ sideFaces M w ∧
      Relation.ReflTransGen (pinchAbsSub_OutAdj M w) (M.faceOf z) (M.faceOf d₀) :=
    pinchAbsOut_const hM (fun f => f ∉ sideFaces M w ∧
      Relation.ReflTransGen (pinchAbsSub_OutAdj M w) (M.faceOf z) f) hstep z d₀ ⟨hg, .refl⟩
  exact h₀.1 ((mem_sideFaces_iff M w d₀).mpr ⟨d₀, hd₀, .refl _⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_exists

/-- A face class of a list whose edges include those of `w` is a face class of `w`. -/
theorem pinchAbsOut_mono {M : CombMap.{v}} {w l : List M.Dart} {x y : M.Dart}
    (hk : ∀ d, walkKeep M w d → walkKeep M l d)
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M l)) x y) :
    Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x y := by
  induction h with
  | rel a b hr =>
      rcases (show b = M.facePerm a ∨ (¬ walkKeep M l a ∧ b = M.alpha a) from hr) with
        hr | ⟨hn, hr⟩
      · exact .rel _ _ (Or.inl hr)
      · exact .rel _ _ (Or.inr ⟨fun hw => hn (hk a hw), hr⟩)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_mono

/-- **A noncrossing closed walk whose outer cycle follows its boundary has an edge connected
outside.** -/
theorem pinchAbsOut_outside_of_follows {M : CombMap.{v}} {w : List M.Dart}
    (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hf : (hw.outerCycle hM).FollowsBoundary) : pinchAbsSub_Outside M w := by
  intro g h hg hh
  obtain ⟨y, hy, hys, hgy⟩ := pinchAbsOut_exists hM.1 hw.ne_nil hg
  obtain ⟨z, hz, -, hhz⟩ := pinchAbsOut_exists hM.1 hw.ne_nil hh
  have hmem : ∀ u, M.alpha u ∈ w → u ∈ (hw.outerCycle hM).cycle := by
    intro u hu
    show u ∈ w.reverse.map M.alpha
    exact List.mem_map.mpr ⟨M.alpha u, List.mem_reverse.mpr hu, M.alpha_involutive u⟩
  have hk : ∀ d, walkKeep M w d → walkKeep M (hw.outerCycle hM).cycle d := by
    intro d hd
    show d ∈ (hw.outerCycle hM).cycle ∨ M.alpha d ∈ (hw.outerCycle hM).cycle
    rcases (show d ∈ w ∨ M.alpha d ∈ w from hd) with hd | hd
    · exact Or.inr (hmem _ (by rw [M.alpha_involutive d]; exact hd))
    · exact Or.inl (hmem d hd)
  have hyz := pinchAbsOut_mono hk
    ((hw.outerCycle hM).eqvGen_of_mem_of_followsBoundary hf (hmem y hy) (hmem z hz))
  exact hgy.trans ((pinchAbsOut_chain hyz hys).trans (pinchAbsOut_rev hhz))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_outside_of_follows

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
