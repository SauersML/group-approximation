import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepCell
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-47: a turn of the outside walk along a region side

Lane gl-p07-47.  Certifies no printed sentence on its own.

* `witnessStepSide_rel_of_infix`: a consecutive pair of an infix of a chain is related.
* `witnessStepSide_sigma_of_boundaryStep`: a boundary step `d → e` of a face set `R` is
  `e = σ^m (α d)` for some `m ≥ 1`.  Each dart `σ^k (α d)` with `0 < k < m` has both of its faces
  in `R`, because it is crossed by an internal move.
* `witnessStepSide_boundaryStep_of_side`: consecutive darts of a region side `c.sideFrom k` form
  a boundary step of `c.1`.  The side is an infix of the boundary cycle
  (`boundary_decomposition`), and that cycle is a `BoundaryStep` chain (`cycle_chain`).
* `witnessStepSide_sigma_of_rotate`: this is `EnclosedFaceSetSucc.turn_next` moved to a
  rotation of the walk.  If the walk turns at `d` to the first kept dart `σ^m (α d)`, that dart is
  the next one, `d'`.
* `witnessStepSide_not_walkKeep`: a dart with both faces in `R` is not an edge of a walk whose
  darts all look into `F`, when `F` is disjoint from `R`.
* `witnessStepSide_alpha_eq_of_sideTurn`: let `(x, y)` be consecutive in a rotation of
  `invDarts X ow`, and let `α y` be followed on a region side by a dart `g` of `ow`.  Then
  `g = α x`.  The darts strictly between `α y` and `g` in the σ-rotation have both faces in the
  region, so they are not edges of the walk.  Hence `g` is the first kept dart.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **A consecutive pair of an infix of a chain is related.** -/
theorem witnessStepSide_rel_of_infix {β : Type*} {R : β → β → Prop} {L S p q : List β}
    {d e : β} (hL : L.IsChain R) (hinf : S <:+: L) (hS : S = p ++ d :: e :: q) : R d e := by
  obtain ⟨A, B, hAB⟩ := hinf
  exact List.isChain_iff_forall_rel_of_append_cons_cons.mp hL
    (show L = (A ++ p) ++ d :: e :: (q ++ B) by rw [← hAB, hS]; simp)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSide_rel_of_infix

section SideWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

/-- **A boundary step is a σ-rotation past internal darts.** -/
theorem witnessStepSide_sigma_of_boundaryStep {R : Finset X.toCombMap.Face}
    {d e : X.toCombMap.Dart} (h : Embedded.BoundaryStep X R d e) :
    ∃ m, 0 < m ∧ (X.toCombMap.sigma ^ m) (X.toCombMap.alpha d) = e ∧
      ∀ k, 0 < k → k < m →
        X.toCombMap.faceOf ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d)) ∈ R ∧
          X.toCombMap.faceOf
            (X.toCombMap.alpha ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d))) ∈ R := by
  unfold Embedded.BoundaryStep at h
  obtain ⟨-, -, hr⟩ := h
  induction hr with
  | refl =>
    refine ⟨1, Nat.one_pos, ?_, fun k hk hk1 => absurd hk1 (by omega)⟩
    rw [pow_one, PocketRun.facePerm_eq_sigma_alpha]
  | tail _ hmove ih =>
    obtain ⟨m, hm, hme, hmk⟩ := ih
    unfold Embedded.InternalBoundaryMove at hmove
    obtain ⟨hf1, hf2, he⟩ := hmove
    refine ⟨m + 1, Nat.succ_pos m, ?_, ?_⟩
    · rw [pow_succ', Equiv.Perm.mul_apply, hme, he, PocketRun.facePerm_eq_sigma_alpha,
        X.toCombMap.alpha_involutive _]
    · intro k hk hkm
      by_cases hlt : k < m
      · exact hmk k hk hlt
      · have heq : k = m := by omega
        rw [heq, hme]
        exact ⟨hf1, hf2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSide_sigma_of_boundaryStep

/-- **Consecutive darts of a region side form a boundary step of the region.** -/
theorem witnessStepSide_boundaryStep_of_side (c : RegionCandidate D eps X)
    (k : Fin X.rCellCount) {p q : List X.toCombMap.Dart} {d e : X.toCombMap.Dart}
    (h : c.sideFrom k = p ++ d :: e :: q) : Embedded.BoundaryStep X c.1 d e := by
  by_cases hs : c.2.source = k
  · rw [Embedded.RegionCandidate.sideFrom, if_pos hs] at h
    have hinf : c.2.rightSide <:+: c.2.boundary.cycle := by
      rw [c.2.boundary_decomposition]
      exact List.infix_append_of_infix_left (List.infix_append _ _ _)
    exact witnessStepSide_rel_of_infix (R := Embedded.BoundaryStep X c.1)
      c.2.boundary.cycle_chain hinf h
  · rw [Embedded.RegionCandidate.sideFrom, if_neg hs] at h
    have hinf : c.2.leftSide <:+: c.2.boundary.cycle := by
      rw [c.2.boundary_decomposition]
      exact List.infix_append_right
    exact witnessStepSide_rel_of_infix (R := Embedded.BoundaryStep X c.1)
      c.2.boundary.cycle_chain hinf h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSide_boundaryStep_of_side

/-- **The first kept σ-successor is the next dart of any rotation of the outside walk.** -/
theorem witnessStepSide_sigma_of_rotate {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow) {n : ℕ}
    {s t : List X.toCombMap.Dart} {d d' : X.toCombMap.Dart}
    (h : ow.rotate n = s ++ d :: d' :: t) {m : ℕ} (hm : 0 < m)
    (hkeep : walkKeep X.toCombMap ow ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha d)))
    (hfirst : ∀ k, 0 < k → k < m →
      ¬ walkKeep X.toCombMap ow ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d))) :
    (X.toCombMap.sigma ^ m) (X.toCombMap.alpha d) = d' := by
  have hlen : s.length + 1 < (ow.rotate n).length := by
    rw [h, List.length_append, List.length_cons, List.length_cons]
    omega
  have hpos : 0 < ow.length := by
    rw [← List.length_rotate ow n]
    omega
  have hp : (s.length + n) % ow.length < ow.length := Nat.mod_lt _ hpos
  have e0 : (ow.rotate n)[s.length]'(by omega) = d := List.getElem_of_append h rfl
  have h' : ow.rotate n = (s ++ [d]) ++ d' :: t := by simp [h]
  have e1 : (ow.rotate n)[s.length + 1]'hlen = d' := List.getElem_of_append h' (by simp)
  have hq : ow[(s.length + n) % ow.length]'hp = d := by
    rw [← e0, List.getElem_rotate]
  have hq1 : ow[((s.length + n) % ow.length + 1) % ow.length]'(Nat.mod_lt _ hpos) = d' := by
    rw [← e1, List.getElem_rotate]
    exact PocketRun.getElem_idx_congr ow
      (by rw [Nat.mod_add_mod, Nat.add_right_comm s.length n 1]) _ _
  have hstep := E.turn_next ((s.length + n) % ow.length) hp m hm
    (by rw [hq]; exact hkeep) (fun k hk hkm => by rw [hq]; exact hfirst k hk hkm)
  calc (X.toCombMap.sigma ^ m) (X.toCombMap.alpha d)
      = (X.toCombMap.sigma ^ m) (X.toCombMap.alpha (ow[(s.length + n) % ow.length]'hp)) := by
        rw [hq]
    _ = ow[((s.length + n) % ow.length + 1) % ow.length]'(Nat.mod_lt _ hpos) := hstep
    _ = d' := hq1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSide_sigma_of_rotate

/-- **A dart with both faces in `R` is not an edge of a walk looking into `F`, off `R`.** -/
theorem witnessStepSide_not_walkKeep {F R : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart}
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    (hR : ∀ f ∈ F, f ∉ R) {z : X.toCombMap.Dart}
    (h1 : X.toCombMap.faceOf z ∈ R) (h2 : X.toCombMap.faceOf (X.toCombMap.alpha z) ∈ R) :
    ¬ walkKeep X.toCombMap ow z := by
  intro hk
  unfold SimpleClosedWalkSides.walkKeep at hk
  rcases hk with hz | hz
  · exact hR _ (hnb z hz) h2
  · have hf := hnb _ hz
    rw [X.toCombMap.alpha_involutive z] at hf
    exact hR _ hf h1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSide_not_walkKeep

/-- **A turn of the inverse walk along a region side.**  If `(x, y)` is consecutive in a rotation
of `invDarts X ow`, and `α y` is followed on the side `c.sideFrom k` by a dart `g` of `ow`, then
`g = α x`, provided the walk's darts look into `F` and `F` is disjoint from `c.1`. -/
theorem witnessStepSide_alpha_eq_of_sideTurn {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    {c : RegionCandidate D eps X} {k : Fin X.rCellCount} (hR : ∀ f ∈ F, f ∉ c.1)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t)
    {p q : List X.toCombMap.Dart} {g : X.toCombMap.Dart}
    (hS : c.sideFrom k = p ++ X.toCombMap.alpha y :: g :: q) (hg : g ∈ ow) :
    g = X.toCombMap.alpha x := by
  have h0 : (ow.reverse.map X.toCombMap.alpha).rotate n = s ++ x :: y :: t := h
  have hr := witnessStep_rotate_of_rotate_inv X.toCombMap.alpha_involutive h0
  obtain ⟨m, hm, hme, hmk⟩ :=
    witnessStepSide_sigma_of_boundaryStep (witnessStepSide_boundaryStep_of_side c k hS)
  have hkeep : walkKeep X.toCombMap ow
      ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha (X.toCombMap.alpha y))) := by
    rw [hme]
    exact Or.inl hg
  have hfirst : ∀ r, 0 < r → r < m → ¬ walkKeep X.toCombMap ow
      ((X.toCombMap.sigma ^ r) (X.toCombMap.alpha (X.toCombMap.alpha y))) :=
    fun r hr0 hrm => witnessStepSide_not_walkKeep hnb hR (hmk r hr0 hrm).1 (hmk r hr0 hrm).2
  exact hme.symm.trans (witnessStepSide_sigma_of_rotate E hr hm hkeep hfirst)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSide_alpha_eq_of_sideTurn

end SideWalk

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
