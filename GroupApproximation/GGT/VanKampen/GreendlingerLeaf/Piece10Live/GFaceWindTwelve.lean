import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindNine
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: an explicit two-lobe witness for the arc-keeping statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-71.

Target of the lane: `gfaceWindNine_Statement` unconditionally.  **NOT CLOSED.**

**LOUD: the suggested single-step route is FALSE.**  Under `¬ gfaceChoose_Loop K` with a
NONEMPTY target arc, no state one excision step from the start is an arc-keeping winding
choice (scratchpad `gl-p10-71/twelve.py`: 0 one-step witnesses among the no-loop cases with a
nonempty target arc, on the models of `gl-p10-61/six.py`, random seeds 1, 3, witness seed 2).
Mechanism: an inner excision keeping the arcs is a `gfaceChoose_Loop` choice (option 2 when the
base face is off the side of the stretch, option 3 when it is on it), and a wrap step with a
nonempty tail cuts the last dart of the pocket walk, a target dart.  Minimal witness depth is
always at most 2 there (13264 at depth 1 / 20594 at depth 2, seed 1; 6835 / 5902, seed 2;
26727 / 46254, seed 3 with one kept cell), depth 1 occurring only for an empty target arc.

Route.  The residual gives the witness state of `gfaceWindNine_Arcs K` as an EXPLICIT list form
of at most two excised simple closed stretches, with `g` the explicit winding formula:

* `Lin` : `∂K = u ++ A ++ w`, state `(u ++ w, 1_K - wind A)` (one inner step);
* `Wr`  : `∂K = z₁ ++ m ++ z₂`, state `(m, 1_K - wind (z₂ ++ z₁))` (one wrap step);
* `LL`  : `∂K = u ++ A ++ v ++ B ++ w`, state `(u ++ v ++ w, 1_K - wind A - wind B)`;
* `WL`  : `∂K = z₁ ++ v₁ ++ A ++ v₂ ++ z₂`, state `(v₁ ++ v₂, 1_K - wind (z₂ ++ z₁) - wind A)`.

The two-step forms are the ones the models use when the target arc is nonempty: one stretch is
a hole (base face on its side), the other an outer lobe.

* `gfaceWindTwelve_inner`, `gfaceWindTwelve_wrap`, `gfaceWindTwelve_two_inner`,
  `gfaceWindTwelve_wrap_inner` (proved): the explicit excision sequences.
* `gfaceWindTwelve_Lobes K` (definition), `gfaceWindTwelve_arcs_of_lobes` (proved).
* `gfaceWindTwelve_Statement` (OPEN), `gfaceWindTwelve_nine_of_statement`,
  `gfaceWindTwelve_six_of_statement`, `gfaceWindTwelve_extremal` (proved).

**LOUD: `gfaceWindTwelve_Statement` is logically STRONGER than `gfaceWindNine_Statement`, not
weaker** (it bounds the sequence by two steps of the four explicit shapes; no converse is
proved).  It is **strictly smaller in proof content**: the `TransGen` excision sequence, the
step decompositions and the face-function bookkeeping are gone (proved here); what remains is
the choice of at most two stretches, their simplicity, and the passing clauses (`0/1`, the arcs
in `c`, clauses 4 and 5) at the explicit state.

## Truth check

Scratchpad `gl-p10-71/forms.py` (extends `gl-p10-66/nine.py`; Lean-faithful loop computed on the
Lean list `∂K = firstSide ++ inv source ++ secondSide ++ target`): every no-loop case has a
witness of shape `Wr`, `LL` or `WL` (not even `Lin` is needed) whose stretches avoid both arcs,
with `g` `0/1` and all passing clauses: 16935 of 16935 (witness seed 2), 24229 of 24229 (random
seed 1); 0 failures.  The searches do not model least area or labels.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

section Steps

variable {M : CombMap.{v}} {o : M.Face}

/-- **One explicit inner excision**: `C = u ++ A ++ w` with `A` simple closed. -/
theorem gfaceWindTwelve_inner {C : List M.Dart} {g : M.Face → ℤ} (u A w : List M.Dart)
    (h : C = u ++ A ++ w) (hA : IsSimpleClosedWalk M A) :
    gfaceWind_Step M o (C, g) (u ++ w, fun f => g f - gfaceWind_wind M o A f) :=
  ⟨u, A, w, h, Or.inl ⟨hA, rfl, rfl⟩⟩

/-- **One explicit wrap excision**: `C = z₁ ++ m ++ z₂` with `z₂ ++ z₁` simple closed. -/
theorem gfaceWindTwelve_wrap {C : List M.Dart} {g : M.Face → ℤ} (z₁ m z₂ : List M.Dart)
    (h : C = z₁ ++ m ++ z₂) (hZ : IsSimpleClosedWalk M (z₂ ++ z₁)) :
    gfaceWind_Step M o (C, g) (m, fun f => g f - gfaceWind_wind M o (z₂ ++ z₁) f) :=
  ⟨z₁, m, z₂, h, Or.inr ⟨hZ, rfl, rfl⟩⟩

/-- **Two explicit inner excisions**: `C = u ++ A ++ v ++ B ++ w`, first `A`, then `B`. -/
theorem gfaceWindTwelve_two_inner {C : List M.Dart} {g : M.Face → ℤ}
    (u A v B w : List M.Dart) (h : C = u ++ A ++ v ++ B ++ w)
    (hA : IsSimpleClosedWalk M A) (hB : IsSimpleClosedWalk M B) :
    Relation.TransGen (gfaceWind_Step M o) (C, g)
      (u ++ v ++ w, fun f => g f - gfaceWind_wind M o A f - gfaceWind_wind M o B f) := by
  have e₁ : C = u ++ A ++ (v ++ B ++ w) := by simp only [h, List.append_assoc]
  have s₁ : gfaceWind_Step M o (C, g)
      (u ++ (v ++ B ++ w), fun f => g f - gfaceWind_wind M o A f) :=
    gfaceWindTwelve_inner u A (v ++ B ++ w) e₁ hA
  have e₂ : u ++ (v ++ B ++ w) = u ++ v ++ B ++ w := by simp only [List.append_assoc]
  have s₂ : gfaceWind_Step M o (u ++ (v ++ B ++ w), fun f => g f - gfaceWind_wind M o A f)
      (u ++ v ++ w, fun f => g f - gfaceWind_wind M o A f - gfaceWind_wind M o B f) :=
    gfaceWindTwelve_inner (u ++ v) B w e₂ hB
  exact Relation.TransGen.tail (Relation.TransGen.single s₁) s₂

/-- **A wrap excision, then an inner one**: `C = z₁ ++ v₁ ++ A ++ v₂ ++ z₂`, first the wrapping
stretch `z₂ ++ z₁`, then `A`. -/
theorem gfaceWindTwelve_wrap_inner {C : List M.Dart} {g : M.Face → ℤ}
    (z₁ v₁ A v₂ z₂ : List M.Dart) (h : C = z₁ ++ v₁ ++ A ++ v₂ ++ z₂)
    (hZ : IsSimpleClosedWalk M (z₂ ++ z₁)) (hA : IsSimpleClosedWalk M A) :
    Relation.TransGen (gfaceWind_Step M o) (C, g)
      (v₁ ++ v₂, fun f => g f - gfaceWind_wind M o (z₂ ++ z₁) f - gfaceWind_wind M o A f) := by
  have e₁ : C = z₁ ++ (v₁ ++ A ++ v₂) ++ z₂ := by simp only [h, List.append_assoc]
  have s₁ : gfaceWind_Step M o (C, g)
      (v₁ ++ A ++ v₂, fun f => g f - gfaceWind_wind M o (z₂ ++ z₁) f) :=
    gfaceWindTwelve_wrap z₁ (v₁ ++ A ++ v₂) z₂ e₁ hZ
  have s₂ : gfaceWind_Step M o
      (v₁ ++ A ++ v₂, fun f => g f - gfaceWind_wind M o (z₂ ++ z₁) f)
      (v₁ ++ v₂, fun f => g f - gfaceWind_wind M o (z₂ ++ z₁) f - gfaceWind_wind M o A f) :=
    gfaceWindTwelve_inner v₁ A v₂ rfl hA
  exact Relation.TransGen.tail (Relation.TransGen.single s₁) s₂

end Steps

section Lobes

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The passing clauses of an arc-keeping winding choice at a state** (the conjuncts of
`gfaceWindNine_Arcs K` after the excision sequence). -/
def gfaceWindTwelve_Good (K : PocketFaceSet D eps X lo hi) (c : List X.toCombMap.Dart)
    (g : X.toCombMap.Face → ℤ) : Prop :=
  ((∀ f, g f = 0 ∨ g f = 1) ∨ ((c.map X.toCombMap.vertexOf).Nodup ∧ ∀ f, 0 ≤ g f)) ∧
    (∀ d ∈ invDarts X K.sourceArc.darts, d ∈ c) ∧ (∀ d ∈ K.targetArc.darts, d ∈ c) ∧
    (K.sourceArc.darts ≠ [] ∨ gfaceWindNine_C4 K c g) ∧ gfaceWindNine_C5 K c g

/-- **An arc-keeping winding choice from a reached state satisfying the passing clauses.** -/
theorem gfaceWindTwelve_arcs_of_reach (K : PocketFaceSet D eps X lo hi)
    {c : List X.toCombMap.Dart} {g : X.toCombMap.Face → ℤ}
    (hr : Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g))
    (hg : gfaceWindTwelve_Good K c g) : gfaceWindNine_Arcs K :=
  ⟨c, g, hr, hg⟩

/-- **An explicit two-lobe witness**: the pocket walk splits as one of the four explicit shapes
`Lin`, `Wr`, `LL`, `WL` (module docstring) with simple closed excised stretches, and the
passing clauses hold at the explicit resulting state. -/
def gfaceWindTwelve_Lobes (K : PocketFaceSet D eps X lo hi) : Prop :=
  (∃ u A w : List X.toCombMap.Dart, K.boundary.cycle = u ++ A ++ w ∧
      IsSimpleClosedWalk X.toCombMap A ∧
      gfaceWindTwelve_Good K (u ++ w) (fun f =>
        gfaceWind_ind K.faces f - gfaceWind_wind X.toCombMap X.outerFace A f)) ∨
    (∃ z₁ m z₂ : List X.toCombMap.Dart, K.boundary.cycle = z₁ ++ m ++ z₂ ∧
      IsSimpleClosedWalk X.toCombMap (z₂ ++ z₁) ∧
      gfaceWindTwelve_Good K m (fun f =>
        gfaceWind_ind K.faces f - gfaceWind_wind X.toCombMap X.outerFace (z₂ ++ z₁) f)) ∨
    (∃ u A v B w : List X.toCombMap.Dart, K.boundary.cycle = u ++ A ++ v ++ B ++ w ∧
      IsSimpleClosedWalk X.toCombMap A ∧ IsSimpleClosedWalk X.toCombMap B ∧
      gfaceWindTwelve_Good K (u ++ v ++ w) (fun f =>
        gfaceWind_ind K.faces f - gfaceWind_wind X.toCombMap X.outerFace A f -
          gfaceWind_wind X.toCombMap X.outerFace B f)) ∨
    (∃ z₁ v₁ A v₂ z₂ : List X.toCombMap.Dart,
      K.boundary.cycle = z₁ ++ v₁ ++ A ++ v₂ ++ z₂ ∧
      IsSimpleClosedWalk X.toCombMap (z₂ ++ z₁) ∧ IsSimpleClosedWalk X.toCombMap A ∧
      gfaceWindTwelve_Good K (v₁ ++ v₂) (fun f =>
        gfaceWind_ind K.faces f - gfaceWind_wind X.toCombMap X.outerFace (z₂ ++ z₁) f -
          gfaceWind_wind X.toCombMap X.outerFace A f))

/-- **The arc-keeping winding choice from an explicit two-lobe witness**: each shape is reached
by its explicit excision sequence. -/
theorem gfaceWindTwelve_arcs_of_lobes (K : PocketFaceSet D eps X lo hi)
    (h : gfaceWindTwelve_Lobes K) : gfaceWindNine_Arcs K := by
  rcases h with ⟨u, A, w, hC, hA, hg⟩ | ⟨z₁, m, z₂, hC, hZ, hg⟩ |
      ⟨u, A, v, B, w, hC, hA, hB, hg⟩ | ⟨z₁, v₁, A, v₂, z₂, hC, hZ, hA, hg⟩
  · exact gfaceWindTwelve_arcs_of_reach K
      (Relation.TransGen.single (gfaceWindTwelve_inner u A w hC hA)) hg
  · exact gfaceWindTwelve_arcs_of_reach K
      (Relation.TransGen.single (gfaceWindTwelve_wrap z₁ m z₂ hC hZ)) hg
  · exact gfaceWindTwelve_arcs_of_reach K (gfaceWindTwelve_two_inner u A v B w hC hA hB) hg
  · exact gfaceWindTwelve_arcs_of_reach K
      (gfaceWindTwelve_wrap_inner z₁ v₁ A v₂ z₂ hC hZ hA) hg

end Lobes

/-- **The explicit two-lobe statement** (OPEN; logically STRONGER than
`gfaceWindNine_Statement`, strictly smaller in proof content, see the module docstring).  Under
the premises of `gfaceWindSix_Statement`, an explicit two-lobe witness exists. -/
def gfaceWindTwelve_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
        gfaceWindTwelve_Lobes K

/-- **`gfaceWindNine_Statement` from the explicit two-lobe statement.** -/
theorem gfaceWindTwelve_nine_of_statement (h : gfaceWindTwelve_Statement.{u, w, v}) :
    gfaceWindNine_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL
  exact gfaceWindTwelve_arcs_of_lobes K
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL)

/-- **`gfaceWindSix_Statement` from the explicit two-lobe statement.** -/
theorem gfaceWindTwelve_six_of_statement (h : gfaceWindTwelve_Statement.{u, w, v}) :
    gfaceWindSix_Statement.{u, w, v} :=
  gfaceWindNine_six_of_statement (gfaceWindTwelve_nine_of_statement h)

/-- **The face-set flip statement from the explicit two-lobe statement.** -/
theorem gfaceWindTwelve_extremal (h : gfaceWindTwelve_Statement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} :=
  gfaceWindNine_extremal (gfaceWindTwelve_nine_of_statement h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_inner
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_wrap
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_two_inner
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_wrap_inner
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_Good
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_arcs_of_reach
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_Lobes
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_arcs_of_lobes
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_Statement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_nine_of_statement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_six_of_statement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindTwelve_extremal
