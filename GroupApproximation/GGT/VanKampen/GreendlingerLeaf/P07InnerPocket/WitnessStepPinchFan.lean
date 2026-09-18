import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSkipVertex
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-52: σ-fans off the enclosed faces

Lane gl-p07-52.  Certifies no printed sentence on its own.  NOT COMPILED.

A **fan** `WitnessStepPinchFan M F y g` is a σ-rotation `g = σ^m y` with `m ≥ 1` whose inner
darts `σ^k y` (`0 < k < m`) have both faces off `F`.
* `witnessStepPinch_fan_trans`: fans compose through a middle dart with both faces off `F`.
* `witnessStepPinch_fan_of_facePerm`: a face step `facePerm d = g` is a fan from `α d` (`m = 1`).
* `witnessStepPinch_fan_of_boundaryStep`: a boundary step of a face set disjoint from `F` is a
  fan (`witnessStepSide_sigma_of_boundaryStep`).
* `witnessStepPinch_fan_vertexOf`: a fan keeps the vertex.
* `witnessStepPinch_alpha_eq_of_fan`: if the end of a fan from `α (α y)` is on the walk, it is the
  next walk dart `α x`.  The inner darts are not walk edges.
* `witnessStepPinch_step_or_pinch_of_fan`: at a junction with a fan, either the forward step
  holds (given it for `g = α x`) or the pair is a pinch.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **A σ-fan from `y` to `g` off the face set `F`.** -/
def WitnessStepPinchFan (M : CombMap.{v}) (F : Finset M.Face) (y g : M.Dart) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (M.sigma ^ m) y = g ∧ ∀ k : ℕ, 0 < k → k < m →
    M.faceOf ((M.sigma ^ k) y) ∉ F ∧ M.faceOf (M.alpha ((M.sigma ^ k) y)) ∉ F

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepPinchFan

/-- **Fans compose** through a middle dart with both faces off `F`. -/
theorem witnessStepPinch_fan_trans {M : CombMap.{v}} {F : Finset M.Face} {y z g : M.Dart}
    (h1 : WitnessStepPinchFan M F y z) (h2 : WitnessStepPinchFan M F z g)
    (hz1 : M.faceOf z ∉ F) (hz2 : M.faceOf (M.alpha z) ∉ F) : WitnessStepPinchFan M F y g := by
  obtain ⟨m₁, -, he₁, hk₁⟩ := h1
  obtain ⟨m₂, hm₂, he₂, hk₂⟩ := h2
  have hpow : ∀ k : ℕ, (M.sigma ^ (k + m₁)) y = (M.sigma ^ k) z := fun k => by
    rw [pow_add, Equiv.Perm.mul_apply, he₁]
  refine ⟨m₂ + m₁, by omega, by rw [hpow, he₂], fun k hk hkm => ?_⟩
  rcases lt_trichotomy k m₁ with hlt | hke | hgt
  · exact hk₁ k hk hlt
  · rw [hke, he₁]
    exact ⟨hz1, hz2⟩
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, k = r + m₁ := ⟨k - m₁, by omega⟩
    rw [hpow]
    exact hk₂ r (by omega) (by omega)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_fan_trans

/-- **A face step is a fan** from the reverse dart, with no inner darts. -/
theorem witnessStepPinch_fan_of_facePerm {M : CombMap.{v}} {F : Finset M.Face} {d g : M.Dart}
    (h : M.facePerm d = g) : WitnessStepPinchFan M F (M.alpha d) g :=
  ⟨1, Nat.one_pos, by rw [pow_one]; exact (PocketRun.facePerm_eq_sigma_alpha d).symm.trans h,
    fun _ hk hk1 => absurd hk1 (by omega)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_fan_of_facePerm

/-- **A fan keeps the vertex.** -/
theorem witnessStepPinch_fan_vertexOf {M : CombMap.{v}} {F : Finset M.Face} {y g : M.Dart}
    (h : WitnessStepPinchFan M F y g) : M.vertexOf g = M.vertexOf y := by
  obtain ⟨m, -, he, -⟩ := h
  rw [← he]
  exact PocketRun.vertexOf_sigma_pow m y

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_fan_vertexOf

section FanWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A boundary step of a face set disjoint from `F` is a fan.** -/
theorem witnessStepPinch_fan_of_boundaryStep {F R : Finset X.toCombMap.Face}
    {d e : X.toCombMap.Dart} (h : Embedded.BoundaryStep X R d e) (hR : ∀ f ∈ F, f ∉ R) :
    WitnessStepPinchFan X.toCombMap F (X.toCombMap.alpha d) e := by
  obtain ⟨m, hm, he, hk⟩ := witnessStepSide_sigma_of_boundaryStep h
  exact ⟨m, hm, he, fun k h0 h1 =>
    ⟨fun hf => hR _ hf (hk k h0 h1).1, fun hf => hR _ hf (hk k h0 h1).2⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_fan_of_boundaryStep

/-- **A dart with both faces off `F` is not an edge of a walk looking into `F`.** -/
theorem witnessStepPinch_not_walkKeep {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart}
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F) {z : X.toCombMap.Dart}
    (h1 : X.toCombMap.faceOf z ∉ F) (h2 : X.toCombMap.faceOf (X.toCombMap.alpha z) ∉ F) :
    ¬ walkKeep X.toCombMap ow z := by
  intro hk
  unfold SimpleClosedWalkSides.walkKeep at hk
  rcases hk with hz | hz
  · exact h2 (hnb z hz)
  · have hf := hnb _ hz
    rw [X.toCombMap.alpha_involutive z] at hf
    exact h1 hf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_not_walkKeep

/-- **The end of a fan on the walk is the next walk dart.**  Let `(x, y)` be consecutive in a
rotation of `invDarts X ow`.  If a fan from `α (α y)` ends at a dart `g` of `ow`, then `g = α x`:
the inner darts of the fan are not walk edges, so `g` is the first kept dart. -/
theorem witnessStepPinch_alpha_eq_of_fan {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t) {g : X.toCombMap.Dart}
    (hfan : WitnessStepPinchFan X.toCombMap F (X.toCombMap.alpha (X.toCombMap.alpha y)) g)
    (hg : g ∈ ow) : g = X.toCombMap.alpha x := by
  have h0 : (ow.reverse.map X.toCombMap.alpha).rotate n = s ++ x :: y :: t := h
  have hr := witnessStep_rotate_of_rotate_inv X.toCombMap.alpha_involutive h0
  obtain ⟨m, hm, hme, hmk⟩ := hfan
  have hkeep : walkKeep X.toCombMap ow
      ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha (X.toCombMap.alpha y))) := by
    rw [hme]
    exact Or.inl hg
  have hfirst : ∀ r, 0 < r → r < m → ¬ walkKeep X.toCombMap ow
      ((X.toCombMap.sigma ^ r) (X.toCombMap.alpha (X.toCombMap.alpha y))) :=
    fun r hr0 hrm => witnessStepPinch_not_walkKeep hnb (hmk r hr0 hrm).1 (hmk r hr0 hrm).2
  exact hme.symm.trans (witnessStepSide_sigma_of_rotate E hr hm hkeep hfirst)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_alpha_eq_of_fan

/-- **A junction with a fan gives the forward step or a pinch.**  If the junction dart `g` is on
the walk, it is `α x` and `hfwd` applies.  Otherwise the fan and the walk successor both start at
the vertex of `y`, so the pair is a pinch across the junction. -/
theorem witnessStepPinch_step_or_pinch_of_fan {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t) {g : X.toCombMap.Dart}
    (hfan : WitnessStepPinchFan X.toCombMap F (X.toCombMap.alpha (X.toCombMap.alpha y)) g)
    (hJ : WitnessStepPinchJunctionNext a b G₁ G₂ (X.toCombMap.alpha y) g)
    (hfwd : g = X.toCombMap.alpha x →
      WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y ∨
      WitnessStepPinchAt a b G₁ G₂ ow x y := by
  by_cases hg : g ∈ ow
  · exact Or.inl (hfwd (witnessStepPinch_alpha_eq_of_fan E hnb h hfan hg))
  · refine Or.inr ⟨g, Or.inr hJ, hg, ?_⟩
    rw [witnessStepPinch_fan_vertexOf hfan, X.toCombMap.alpha_involutive y]
    exact (witnessStepSkip_vertexOf_of_rotate E h).symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_step_or_pinch_of_fan

end FanWalk

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
