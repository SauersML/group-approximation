import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchArcStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchArcList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchArcClassify
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchParityProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-57: the entry-step residual from the curve-first residual

Lane gl-p07-57.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepPinchArc_parity_of_arc`: `WitnessStepPinchParityStatement` from
  `WitnessStepPinchArcStatement`.  Descent induction on the length of the prefix before `y`.
* `witnessStepPinchArc_arc_of_parity`: the converse (drop the extra hypothesis).
* `witnessStepPinchArc_iff_parity`: LOUD, the two are equivalent.
* `witnessStepPinchArc_skip_of_arc`: the wire to `WitnessStepSkipStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-57: the entry-step residual from the curve-first residual.**  At an off-lobe
pinch `(x, y)` with `w = pre ++ y :: (mid ++ x :: post)`, the prefix `pre` is off `l`, by
induction on `pre.length`.  A dart of `pre` on `l` gives an entry step `(x', y')` into `pre`
(`witnessStepPinchParity_entry`).  By `witnessStepPinchArc_classify` that step is one of three
kinds.  (1) A forward `StepNext` with `x'` before `y'`: then `x' ∈ pre`, which is impossible.
(2) A forward `StepNext` with `y'` curve-first: this is excluded by the hypothesis.  (3) An
off-lobe pinch: its prefix `p` before `y'` is shorter than `pre`, so it is off `l` by induction,
and `y'` is curve-first, which is again excluded.  The entry step of the parity statement then
has `y' ∈ pre ∩ l`, a contradiction. -/
theorem witnessStepPinchArc_parity_of_arc (h : WitnessStepPinchArcStatement.{u, w, v}) :
    WitnessStepPinchParityStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · have hnd := witnessSublist_curve_nodup a b G₁ G₂
    have key : ∀ (k n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
        (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
        ¬ WitnessStepCellTurn G₁ G₂ outerWalk y →
        ¬ WitnessStepSideTurn a b G₁ G₂ outerWalk y →
        ¬ WitnessStepBlockTurn a b G₁ G₂ x y →
        ¬ WitnessStepCornerTurn a b G₁ G₂ outerWalk y →
        WitnessStepPinchOffAt a b K C.face G₁ G₂ outerWalk x y →
        ∀ pre mid post : List X.toCombMap.Dart,
          witnessSublistCurve a b G₁ G₂ = pre ++ y :: (mid ++ x :: post) →
          pre.length ≤ k → ∀ e ∈ pre, e ∉ invDarts X outerWalk := by
      intro k
      induction k with
      | zero =>
        intro _ _ _ _ _ _ _ _ _ _ _ pre _ _ _ hlen e he _
        have hpos := List.length_pos_of_mem he
        omega
      | succ k ih =>
        intro n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve hlen e he hel
        obtain ⟨n', s', x', y', t', hr', hx', hy'⟩ :=
          witnessStepPinchParity_entry hel he (witnessStepPinchParity_mem_of_rotate hr)
            (witnessStepPinchParity_not_mem_pre hnd hcurve)
        have hx'l : x' ∈ invDarts X outerWalk :=
          (List.mem_rotate (n := n')).mp (by rw [hr']; simp)
        rcases witnessStepPinchArc_classify hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hG₁ hG₂ hw hCa
            hCb E hnb hlab hr' with hstep | ⟨hc', hs', hb', hco', hp'⟩
        · unfold WitnessCurveSublistList.StepNext at hstep
          rcases hstep with ⟨u', v', z', h1⟩ | ⟨u', z', h2, hu'⟩
          · exact hx' (witnessStepPinchArc_mem_pre_of_before hnd hcurve h1 hy')
          · exact hfwd n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve n' s'
              t' x' y' hr' hx' hy' (witnessStepPinchParity_face_of_rotate hnb hr')
              (witnessStepPinchParity_turn_fan E hr') ⟨u', z', h2, hu'⟩
        · obtain ⟨p, mid', post', hsplit, hplen⟩ := witnessStepPinchArc_split_after hcurve hy'
            (witnessSublist_mem_curve (hlab x' hx'l)) hx'
          exact hfwd n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve n' s' t'
            x' y' hr' hx' hy' (witnessStepPinchParity_face_of_rotate hnb hr')
            (witnessStepPinchParity_turn_fan E hr')
            ⟨p, mid' ++ x' :: post', hsplit,
              ih n' s' t' x' y' hr' hc' hs' hb' hco' hp' p mid' post' hsplit (by omega)⟩
    refine Or.inl fun n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve n' s' t'
      x' y' hr' _ hy' _ _ => ?_
    exact key pre.length n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve
      le_rfl y' hy' (witnessStepPinchParity_mem_of_rotate hr')
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchArc_parity_of_arc

/-- **The converse.**  The parity residual drops the extra curve-first hypothesis. -/
theorem witnessStepPinchArc_arc_of_parity (h : WitnessStepPinchParityStatement.{u, w, v}) :
    WitnessStepPinchArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · exact Or.inl fun n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve n' s' t'
      x' y' hr' hx' hy' hF hfan _ =>
      hfwd n s t x y hr hcell hside hblock hcorner hpinch pre mid post hcurve n' s' t' x' y' hr'
        hx' hy' hF hfan
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchArc_arc_of_parity

/-- **LOUD: the curve-first residual is equivalent to the entry-step residual.**  It is strictly
smaller only in proof content. -/
theorem witnessStepPinchArc_iff_parity :
    WitnessStepPinchArcStatement.{u, w, v} ↔ WitnessStepPinchParityStatement.{u, w, v} :=
  ⟨witnessStepPinchArc_parity_of_arc, witnessStepPinchArc_arc_of_parity⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchArc_iff_parity

/-- **The skip residual from the curve-first residual.** -/
theorem witnessStepPinchArc_skip_of_arc (h : WitnessStepPinchArcStatement.{u, w, v}) :
    WitnessStepSkipStatement.{u, w, v} :=
  witnessStepPinchParity_skip_of_parity (witnessStepPinchArc_parity_of_arc h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchArc_skip_of_arc

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
