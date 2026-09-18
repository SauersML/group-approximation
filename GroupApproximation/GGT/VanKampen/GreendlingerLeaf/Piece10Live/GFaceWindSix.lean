import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindSixIter
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindFive
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'` off the loop pockets: `0/1` and clauses 4, 5 from walk regions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-61.

Route.  The residual `gfaceWindFive_Statement` asks, on no-loop pockets, for
`gfaceWindClause_Choice K`: a nonempty excision sequence to `(c, g)` with `g` `0/1`-valued,
clause 4 (source face out, or `SrcOut`), clause 5 (a kept cell in the support of `g`) and
clauses 8, 9.  Three of these are discharged from the reached walk `c` itself:

* `0/1`: it suffices that `c` repeats no vertex and `g ≥ 0`.  Then `c` is empty (and `g = 0`,
  `gfaceWindSix_nil`) or a simple closed walk (`gfaceWindSix_bal_reach`, `gfaceWindSix_simple`)
  and `g` is its side indicator (`gfaceWindSix_zero_one`).
* clause 4: it suffices that the source face lies in the `c`-walk region (steps across edges off
  `c`, `gfaceWindClause_Adj`) of the exterior face or of the face across a dart of `c`; `g` is
  constant on such regions (`gfaceWindClause_const`) and `0` at those faces
  (`gfaceWindSix_walk_val`).  This subsumes `SrcOut`, whose region is for the larger walk `C`.
* clause 5: it suffices that some kept cell lies in the `c`-walk region of the face of a dart
  of `c`, where `g = 1`.

* `gfaceWindSix_Choice K` (hypothesis): `gfaceWindClause_Choice K` with these three weakenings.
* `gfaceWindSix_choice` (proved): it gives `gfaceWindClause_Choice K`; the converse
  `gfaceWindSix_of_clause` is proved too.
* `gfaceWindSix_Statement` (OPEN): `gfaceWindFive_Statement` with conclusion
  `gfaceWindSix_Choice K`.
* `gfaceWindSix_five_of_six`, `gfaceWindSix_six_of_five` (proved): the two directions;
  `gfaceWindSix_extremal` (proved): it implies `extremalGFaceProve_Statement`.

**LOUD: the residual is EQUIVALENT to `gfaceWindFive_Statement`, not strictly weaker** (both
directions are proved here).  It is **strictly smaller in proof content**: the `0/1` property is
discharged at every vertex-simple state with `g ≥ 0` (such states are reached from `PosStep`,
`gfaceWindSix_pocket`), clauses 4 and 5 by the `c`-walk regions, and `SrcOut` is subsumed.
**LOUD: the terminal state of `gfaceWindSix_pocket` alone is FALSE as a complete strategy**: it
satisfies the face-set clauses on only a minority of no-loop decompositions (truth check), so
the sequence must still be chosen.

## Truth check

Scratchpad `gl-p10-61/six.py`, `gfaces.py`, `pass.py`, on the Lean-faithful models of
`gl-p10-49/gface.py` and the integer reach of `gl-p10-55/wind.py` (random seeds 1, 3; witness
seed 2).  Terminal vertex-simple states with `g ≥ 0` are `0/1`: 0 failures.  A passing state
is reached along a `g ≥ 0` path in 41423 of 41423 and 15372 of 15372 no-loop cases.  Terminal
states pass in only 2770 of 14416, 4084 of 20984, 0 of 7258 no-loop cases.  The searches do not
model least area, labels or `G`-faces.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

section Six

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A winding choice with region-discharged clauses**: `gfaceWindClause_Choice K` with the
`0/1` clause weakened by the vertex-simple `g ≥ 0` alternative, and clauses 4 and 5 by the
`c`-walk region alternatives. -/
def gfaceWindSix_Choice (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ (c : List X.toCombMap.Dart) (g : X.toCombMap.Face → ℤ),
    Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) ∧
    ((∀ f, g f = 0 ∨ g f = 1) ∨ ((c.map X.toCombMap.vertexOf).Nodup ∧ ∀ f, 0 ≤ g f)) ∧
    ((∃ f, (f = X.outerFace ∨ ∃ x ∈ c, X.toCombMap.faceOf (X.toCombMap.alpha x) = f) ∧
        Relation.ReflTransGen (gfaceWindClause_Adj X.toCombMap c) f (cell X K.source).face) ∨
      (cell X K.source).face ∉ gfaceWind_faces g) ∧
    ((∃ x ∈ c, ∃ kept : Fin X.rCellCount,
        Relation.ReflTransGen (gfaceWindClause_Adj X.toCombMap c) (X.toCombMap.faceOf x)
          (cell X kept).face) ∨
      ∃ kept : Fin X.rCellCount, (cell X kept).face ∈ gfaceWind_faces g) ∧
    (gfaceWindClause_SrcGap K ∨
      ∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
        K.sourceArc.darts.filter (fun d =>
          extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g) (X.toCombMap.alpha d)) = mid) ∧
    (gfaceWindClause_TgtGap K ∨
      ∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
        K.targetArc.darts.filter (extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g)) = mid)

/-- **`0/1` and clauses 4, 5 from the reached walk**: a winding choice with region-discharged
clauses is a winding choice with walk-discharged clauses. -/
theorem gfaceWindSix_choice (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (h : gfaceWindSix_Choice K) : gfaceWindClause_Choice K := by
  obtain ⟨c, g, hr, h01, h4, h5, h8, h9⟩ := h
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
  have h01' : ∀ f, g f = 0 ∨ g f = 1 := by
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
  refine ⟨c, g, hr, h01', Or.inr ?_, ?_, h8, h9⟩
  · rcases h4 with ⟨f, hf, hreach⟩ | hs
    · have hg0 : g f = 0 := by
        rcases hf with rfl | ⟨x, hx, rfl⟩
        · exact ho
        · exact (gfaceWindSix_walk_val hcob h01' hx (hne x hx)).2
      intro hmem
      rw [gfaceWind_mem_faces, ← gfaceWindClause_const (C := c) (fun _ hy => hy) hcob hreach,
        hg0] at hmem
      norm_num at hmem
    · exact hs
  · rcases h5 with ⟨x, hx, kept, hreach⟩ | hs
    · refine ⟨kept, ?_⟩
      rw [gfaceWind_mem_faces, ← gfaceWindClause_const (C := c) (fun _ hy => hy) hcob hreach]
      exact (gfaceWindSix_walk_val hcob h01' hx (hne x hx)).1
    · exact hs

/-- **The converse**: a winding choice with walk-discharged clauses is one with
region-discharged clauses (`SrcOut` is a `C`-walk region condition, hence a `c`-walk one). -/
theorem gfaceWindSix_of_clause (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (h : gfaceWindClause_Choice K) : gfaceWindSix_Choice K := by
  obtain ⟨c, g, hr, h01, h4, h5, h8, h9⟩ := h
  have hc := K.boundary.cycle_mem_iff
  have h0 : gfaceWind_Inv X.toCombMap K.boundary.cycle X.outerFace K.boundary.cycle
      (gfaceWind_ind K.faces) :=
    gfaceWind_inv_start (fun d => (hc d).symm) hK.1 K.outerFace_not_mem
  obtain ⟨⟨hfil, -, -, -⟩, -⟩ :=
    gfaceWind_reach_pair X.planar K.boundary.cycle_nodup hr h0
  have hsub : ∀ x ∈ c, x ∈ K.boundary.cycle := by
    intro x hx
    have hx' : x ∈ K.boundary.cycle.filter (gfaceWind_mem c) := by
      rw [hfil]
      exact hx
    exact (List.mem_filter.mp hx').1
  have hmono : ∀ {a b : X.toCombMap.Face},
      Relation.ReflTransGen (gfaceWindClause_Adj X.toCombMap K.boundary.cycle) a b →
        Relation.ReflTransGen (gfaceWindClause_Adj X.toCombMap c) a b := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      obtain ⟨x, hx1, hx2, h1, h2⟩ := hst
      exact ih.tail ⟨x, fun hx => hx1 (hsub x hx), fun hx => hx2 (hsub _ hx), h1, h2⟩
  refine ⟨c, g, hr, Or.inl h01, ?_, Or.inr h5, h8, h9⟩
  rcases h4 with hs | hs
  · exact Or.inl ⟨X.outerFace, Or.inl rfl, hmono hs⟩
  · exact Or.inr hs

end Six

/-- **The winding flip statement off the loop pockets, region-discharged** (OPEN; EQUIVALENT to
`gfaceWindFive_Statement`, both directions proved, strictly smaller in proof content, see the
module docstring).  Under the premises of `extremalGFaceProve_Statement` and when no loop choice
exists, a winding choice of `F'` with region-discharged clauses exists. -/
def gfaceWindSix_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
        gfaceWindSix_Choice K

/-- **The residual `gfaceWindFive_Statement` from its region-discharged form.** -/
theorem gfaceWindSix_five_of_six (h : gfaceWindSix_Statement.{u, w, v}) :
    gfaceWindFive_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL
  exact gfaceWindSix_choice K hK
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL)

/-- **The converse**: `gfaceWindFive_Statement` gives its region-discharged form. -/
theorem gfaceWindSix_six_of_five (h : gfaceWindFive_Statement.{u, w, v}) :
    gfaceWindSix_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL
  exact gfaceWindSix_of_clause K hK
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL)

/-- **The face-set flip statement from the region-discharged form.** -/
theorem gfaceWindSix_extremal (h : gfaceWindSix_Statement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} :=
  gfaceWindFive_extremal (gfaceWindSix_five_of_six h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_Choice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_choice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_of_clause
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_Statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_five_of_six
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_six_of_five
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_extremal
