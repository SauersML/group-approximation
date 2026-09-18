import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindNineCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: a passing state keeping the source and target arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-66.

Route.  `gfaceWindSix_Statement` asks for `gfaceWindSix_Choice K`, that is
(`gfaceWindNine_choice_iff`) a passing state `gfaceWindNine_Pass K c g` reached by a NONEMPTY
excision sequence.  Two residuals are isolated.

* `gfaceWindNine_ReachStatement` (OPEN): the passing state is reached along a nonempty
  sign-keeping (`g ≥ 0` at every state) path.  `gfaceWindNine_six_of_reach` (proved).
* `gfaceWindNine_Arcs K` (definition): a state reached by a nonempty excision sequence, `0/1`
  (or vertex-simple with `g ≥ 0`), whose walk `c` CONTAINS the inverse source arc and the target
  arc, with clause 5 and, when the source arc is empty, clause 4.
  `gfaceWindNine_pass_of_arcs` (proved): such a state passes, since clauses 8 and 9 hold with
  the filters equal to the whole arcs, and for a nonempty source arc clause 4 holds with the
  source face across a dart of `c` (`gfaceWindNine_pass_of_facts`).
* `gfaceWindNine_Statement` (OPEN): under the premises of `gfaceWindSix_Statement`,
  `gfaceWindNine_Arcs K`.  `gfaceWindNine_six_of_statement`, `gfaceWindNine_extremal` (proved).

**LOUD: both residuals are logically STRONGER than `gfaceWindSix_Statement`, not weaker** (the
first demands a sign-keeping path, the second demands the arcs in `c`; no converse is proved).
`gfaceWindNine_Statement` is **strictly smaller in proof content**: clauses 8 and 9 are gone,
clause 4 is gone for a nonempty source arc, and only `0/1`, clause 5 and the arc containment
remain.  Since steps only shrink the walk, "`c` contains the arcs" is the same as "every state
of the sequence contains the arcs": the sequence must never excise an arc dart.
**LOUD: the reflexive form is trivially true** (`gfaceWindNine_refl_trivial`, the start state
passes), so the nonempty sequence is essential.

FALSE strategies (truth check, scratchpad `gl-p10-66/arcs*.py`, `explore.py`): the terminal
state of arc-keeping sign-keeping paths (passes on 437 of 9382 and 500 of 23376 cases); the
first vertex-simple state; paths of `0/1` states only (9024 of 9382, 3605 of 5229); paths
keeping the source face outside `F'`; greedy innermost or outermost excision; decreasing steps
only (0 of 13670).

## Truth check

Scratchpad `gl-p10-66/nine.py` on the models of `gl-p10-49/gface.py`, `gl-p10-55/wind.py`,
`gl-p10-61/six.py`, `gfaces.py` (random seeds 1, 3; witness seed 2).  A `0/1` passing state
containing both arcs is reached by a nonempty sign-keeping path in all no-loop cases: 13616,
19540, 5861 of 13616, 19540, 5861 (kept: `F' ≠ ∅`) and 11334, 23376, 9201 of 11334, 23376,
9201 (worst `G`-face case, one kept cell); hence `gfaceWindNine_Statement` and
`gfaceWindNine_ReachStatement` hold there.  Empty source arcs (clause 4 kept) are the majority
of the model cases and all pass.  The searches do not model least area or labels.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

section NineArcs

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The invariant facts at a reached state**: coboundary, `0/1` values (from the `0/1` or the
vertex-simple `g ≥ 0` alternative) and no dart of `c` with its reverse in `c`. -/
theorem gfaceWindNine_facts (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {c : List X.toCombMap.Dart} {g : X.toCombMap.Face → ℤ}
    (hr : Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g))
    (h01 : (∀ f, g f = 0 ∨ g f = 1) ∨ ((c.map X.toCombMap.vertexOf).Nodup ∧ ∀ f, 0 ≤ g f)) :
    (∀ d, g (X.toCombMap.faceOf d) - g (X.toCombMap.faceOf (X.toCombMap.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (X.toCombMap.alpha d)) ∧
    (∀ f, g f = 0 ∨ g f = 1) ∧ (∀ x, x ∈ c → X.toCombMap.alpha x ∉ c) := by
  have hc := K.boundary.cycle_mem_iff
  have h0 : gfaceWind_Inv X.toCombMap K.boundary.cycle X.outerFace K.boundary.cycle
      (gfaceWind_ind K.faces) :=
    gfaceWind_inv_start (fun d => (hc d).symm) hK.1 K.outerFace_not_mem
  obtain ⟨⟨hfil, hch, hcob, ho⟩, -⟩ :=
    gfaceWind_reach_pair X.planar K.boundary.cycle_nodup hr h0
  have hsub : ∀ x ∈ c, x ∈ K.boundary.cycle := by
    intro x hx
    have hx' : x ∈ K.boundary.cycle.filter (gfaceWind_mem c) := by
      rw [hfil]
      exact hx
    exact (List.mem_filter.mp hx').1
  have hne : ∀ x, x ∈ c → X.toCombMap.alpha x ∉ c := fun x hx hax =>
    ((hc x).mp (hsub x hx)).2 ((hc _).mp (hsub _ hax)).1
  refine ⟨hcob, ?_, hne⟩
  rcases h01 with h01 | ⟨hnd, hpos⟩
  · exact h01
  · have hbal : gfaceWindSix_Bal X.toCombMap c :=
      gfaceWindSix_bal_reach (s := (K.boundary.cycle, gfaceWind_ind K.faces)) (t := (c, g))
        hr.to_reflTransGen ((gfaceWindSix_bal_iff K.boundary.cycle_nonempty hK.1).mpr hK.2)
    rcases eq_or_ne c [] with hc0 | hc0
    · rw [hc0] at hcob
      exact fun f =>
        Or.inl (gfaceWindSix_nil (X.toCombMap.connected_of_planar X.planar) hcob ho f)
    · have hw := gfaceWindSix_simple hc0 hch hbal hnd hne
      intro f
      rw [(gfaceWindSix_zero_one X.planar hw hcob ho hpos).2 f]
      exact gfaceWindSix_ind01 _ f

/-- **Passing from the arcs at a reached state.** -/
theorem gfaceWindNine_pass_of_arcs (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {c : List X.toCombMap.Dart} {g : X.toCombMap.Face → ℤ}
    (hr : Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g))
    (h01 : (∀ f, g f = 0 ∨ g f = 1) ∨ ((c.map X.toCombMap.vertexOf).Nodup ∧ ∀ f, 0 ≤ g f))
    (hs : ∀ d ∈ invDarts X K.sourceArc.darts, d ∈ c) (ht : ∀ d ∈ K.targetArc.darts, d ∈ c)
    (h4 : K.sourceArc.darts ≠ [] ∨ gfaceWindNine_C4 K c g) (h5 : gfaceWindNine_C5 K c g) :
    gfaceWindNine_Pass K c g := by
  obtain ⟨hcob, h01', hne⟩ := gfaceWindNine_facts K hK hr h01
  exact gfaceWindNine_pass_of_facts K hcob h01' hne hs ht h4 h5

/-- **An arc-keeping winding choice**: a state reached by a nonempty excision sequence, `0/1` or
vertex-simple with `g ≥ 0`, whose walk contains the inverse source arc and the target arc, with
clause 4 when the source arc is empty, and clause 5. -/
def gfaceWindNine_Arcs (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ (c : List X.toCombMap.Dart) (g : X.toCombMap.Face → ℤ),
    Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) ∧
    ((∀ f, g f = 0 ∨ g f = 1) ∨ ((c.map X.toCombMap.vertexOf).Nodup ∧ ∀ f, 0 ≤ g f)) ∧
    (∀ d ∈ invDarts X K.sourceArc.darts, d ∈ c) ∧ (∀ d ∈ K.targetArc.darts, d ∈ c) ∧
    (K.sourceArc.darts ≠ [] ∨ gfaceWindNine_C4 K c g) ∧ gfaceWindNine_C5 K c g

/-- **The winding choice from an arc-keeping one.** -/
theorem gfaceWindNine_choice_of_arcs (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (h : gfaceWindNine_Arcs K) : gfaceWindSix_Choice K := by
  obtain ⟨c, g, hr, h01, hs, ht, h4, h5⟩ := h
  exact (gfaceWindNine_choice_iff K).mpr
    ⟨c, g, hr, gfaceWindNine_pass_of_arcs K hK hr h01 hs ht h4 h5⟩

end NineArcs

/-- **The sign-keeping reach statement** (OPEN; STRONGER than `gfaceWindSix_Statement`, see the
module docstring).  Under the premises of `gfaceWindSix_Statement`, a passing state is reached
along a nonempty path of steps keeping `g ≥ 0`. -/
def gfaceWindNine_ReachStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
        gfaceWindNine_Reach K

/-- **`gfaceWindSix_Statement` from the sign-keeping reach statement.** -/
theorem gfaceWindNine_six_of_reach (h : gfaceWindNine_ReachStatement.{u, w, v}) :
    gfaceWindSix_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL
  exact gfaceWindNine_choice_of_reach K
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL)

/-- **The arc-keeping winding statement** (OPEN; STRONGER than `gfaceWindSix_Statement`,
strictly smaller in proof content, see the module docstring).  Under the premises of
`gfaceWindSix_Statement`, an arc-keeping winding choice exists. -/
def gfaceWindNine_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
        gfaceWindNine_Arcs K

/-- **`gfaceWindSix_Statement` from the arc-keeping winding statement.** -/
theorem gfaceWindNine_six_of_statement (h : gfaceWindNine_Statement.{u, w, v}) :
    gfaceWindSix_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL
  exact gfaceWindNine_choice_of_arcs K hK
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL)

/-- **The face-set flip statement from the arc-keeping winding statement.** -/
theorem gfaceWindNine_extremal (h : gfaceWindNine_Statement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} :=
  gfaceWindSix_extremal (gfaceWindNine_six_of_statement h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_facts
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_pass_of_arcs
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_Arcs
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_choice_of_arcs
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_ReachStatement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_six_of_reach
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_Statement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_six_of_statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindNine_extremal
