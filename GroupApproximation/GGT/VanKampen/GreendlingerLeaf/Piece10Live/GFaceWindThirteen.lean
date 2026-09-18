import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindTwelve
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: the two-lobe witness with nested wraps

Lane gl-p10-73.  Target of the lane: `gfaceWindTwelve_Statement`.  **NOT CLOSED, and
LOUD: `gfaceWindTwelve_Statement` is FALSE on the combinatorial model** (scratchpad
`gl-p10-73/leanexact.py`, `failL.py`, with `gfaceChoose_Loop` and `gfaceWindTwelve_Good`
computed literally).  Counterexample: the map `sig = [11,2,9,8,14,4,7,5,3,13,18,10,0,15,1,6,
12,16,19,17]` of `gl-p10-71/forms.py`, base face `6`, pocket `K = {1,2,3,4,5,7}`, source face
`8`, pocket walk `[3,1,18,11,12,9]`, both arcs empty, and relator cells only the faces `2`
(kept) and `8` (source).  The other inner faces are `0`-cells, which `DiscDiagram.inner_face`
allows.  There `¬ gfaceChoose_Loop K` holds and no shape `Lin`, `Wr`, `LL`, `WL` passes, but the
nested wrap `WW` below does: `z₁ = [3]`, `y₁ = [1]`, `m = [18,11]`, `y₂ = [12]`, `z₂ = [9]`.  The
first wrap `[9,3]` is a hole of `K`; the second, `[12,1]`, is an outer lobe of `K \ {2}`.  Least
area, labels, `eps` and `lo`/`hi` are not modelled, so this is a counterexample to the
combinatorial content, not a formal refutation.

**Correction to gl-p10-71.**  Its docstring says the 21 fixed-kept failures are no
counterexamples because clause 5 is existential.  That holds only if every inner face is a
relator cell.  With the other inner faces `0`-cells, the existential ranges over `{kept,
source}` only, and the failure is genuine.

Residual: the corrected, TRUE-on-the-model statement `gfaceWindThirteen_Statement`, whose
conclusion adds the fifth shape

* `WW` : `∂K = z₁ ++ y₁ ++ m ++ y₂ ++ z₂`, with state
  `(m, 1_K - wind (z₂ ++ z₁) - wind (y₂ ++ y₁))`: a wrap step, then a wrap step of the remainder.

Declarations:

* `gfaceWindThirteen_wrap_wrap` (proved): the two-step excision sequence of `WW`.
* `gfaceWindThirteen_Lobes K` (definition): `gfaceWindTwelve_Lobes K ∨ WW`.
* `gfaceWindThirteen_arcs_of_lobes` and `gfaceWindThirteen_lobes_of_twelve` (proved).
* `gfaceWindThirteen_Statement` (OPEN).
* Proved: `gfaceWindThirteen_of_twelve`, `gfaceWindThirteen_nine_of_statement`,
  `gfaceWindThirteen_six_of_statement`, `gfaceWindThirteen_extremal`.

**Strength.**  `gfaceWindThirteen_Statement` is logically WEAKER than
`gfaceWindTwelve_Statement`; `gfaceWindThirteen_of_twelve` proves this.  It is STRICTLY weaker on
the model: the counterexample above violates Twelve but not Thirteen.  It is still STRONGER than
`gfaceWindNine_Statement`, since it bounds the sequence by two explicit steps.  Its proof content
is the same as Twelve's: choose at most two stretches, prove them simple, and prove the passing
clauses at the explicit state.

## Truth check

Scratchpad `gl-p10-73/leanexact.py` (literal Lean loop and passing clauses; relator cells all
inner faces (`exists`) or only `{kept, source}` (`cell`)).  The counts are in the lane report.
`gl-p10-73/thirteen.py` checks the same shapes against the stronger model clauses of
`gl-p10-55/wind.py`.  **LOUD: typing each stretch as a hole or an outer lobe of the current face
set is FALSE as a complete strategy.**  Some needed witnesses have a middle state that is not
`0/1`.  So the residual keeps the explicit winding formula and does not type the stretches.
Other depth-2 shapes (a wrap inside an inner stretch, or nested inner stretches) are not
included; no model case needed them.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

section Steps

variable {M : CombMap.{v}} {o : M.Face}

/-- **Two nested wrap excisions**: `C = z₁ ++ y₁ ++ m ++ y₂ ++ z₂`, first the wrapping stretch
`z₂ ++ z₁`, then the wrapping stretch `y₂ ++ y₁` of the remainder `y₁ ++ m ++ y₂`. -/
theorem gfaceWindThirteen_wrap_wrap {C : List M.Dart} {g : M.Face → ℤ}
    (z₁ y₁ m y₂ z₂ : List M.Dart) (h : C = z₁ ++ y₁ ++ m ++ y₂ ++ z₂)
    (hZ : IsSimpleClosedWalk M (z₂ ++ z₁)) (hY : IsSimpleClosedWalk M (y₂ ++ y₁)) :
    Relation.TransGen (gfaceWind_Step M o) (C, g)
      (m, fun f => g f - gfaceWind_wind M o (z₂ ++ z₁) f - gfaceWind_wind M o (y₂ ++ y₁) f) := by
  have e₁ : C = z₁ ++ (y₁ ++ m ++ y₂) ++ z₂ := by simp only [h, List.append_assoc]
  have s₁ : gfaceWind_Step M o (C, g)
      (y₁ ++ m ++ y₂, fun f => g f - gfaceWind_wind M o (z₂ ++ z₁) f) :=
    gfaceWindTwelve_wrap z₁ (y₁ ++ m ++ y₂) z₂ e₁ hZ
  have s₂ : gfaceWind_Step M o
      (y₁ ++ m ++ y₂, fun f => g f - gfaceWind_wind M o (z₂ ++ z₁) f)
      (m, fun f => g f - gfaceWind_wind M o (z₂ ++ z₁) f - gfaceWind_wind M o (y₂ ++ y₁) f) :=
    gfaceWindTwelve_wrap y₁ m y₂ rfl hY
  exact Relation.TransGen.tail (Relation.TransGen.single s₁) s₂

end Steps

section Lobes

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **An explicit two-lobe witness with nested wraps**: one of the four shapes of
`gfaceWindTwelve_Lobes K`, or the shape `WW` (module docstring) with simple closed wrapping
stretches, and the passing clauses at the explicit resulting state. -/
def gfaceWindThirteen_Lobes (K : PocketFaceSet D eps X lo hi) : Prop :=
  gfaceWindTwelve_Lobes K ∨
    ∃ z₁ y₁ m y₂ z₂ : List X.toCombMap.Dart,
      K.boundary.cycle = z₁ ++ y₁ ++ m ++ y₂ ++ z₂ ∧
      IsSimpleClosedWalk X.toCombMap (z₂ ++ z₁) ∧ IsSimpleClosedWalk X.toCombMap (y₂ ++ y₁) ∧
      gfaceWindTwelve_Good K m (fun f =>
        gfaceWind_ind K.faces f - gfaceWind_wind X.toCombMap X.outerFace (z₂ ++ z₁) f -
          gfaceWind_wind X.toCombMap X.outerFace (y₂ ++ y₁) f)

/-- **The arc-keeping winding choice from an explicit witness with nested wraps.** -/
theorem gfaceWindThirteen_arcs_of_lobes (K : PocketFaceSet D eps X lo hi)
    (h : gfaceWindThirteen_Lobes K) : gfaceWindNine_Arcs K := by
  rcases h with h | ⟨z₁, y₁, m, y₂, z₂, hC, hZ, hY, hg⟩
  · exact gfaceWindTwelve_arcs_of_lobes K h
  · exact gfaceWindTwelve_arcs_of_reach K
      (gfaceWindThirteen_wrap_wrap z₁ y₁ m y₂ z₂ hC hZ hY) hg

/-- **A two-lobe witness is a witness with nested wraps.** -/
theorem gfaceWindThirteen_lobes_of_twelve (K : PocketFaceSet D eps X lo hi)
    (h : gfaceWindTwelve_Lobes K) : gfaceWindThirteen_Lobes K :=
  Or.inl h

end Lobes

/-- **The explicit statement with nested wraps** (OPEN; logically WEAKER than
`gfaceWindTwelve_Statement`, and STRONGER than `gfaceWindNine_Statement`; see the module
docstring).  Under the premises of `gfaceWindSix_Statement`, an explicit witness with nested
wraps exists. -/
def gfaceWindThirteen_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
        gfaceWindThirteen_Lobes K

/-- **The statement with nested wraps from the two-lobe statement**: the residual is no
stronger than `gfaceWindTwelve_Statement`. -/
theorem gfaceWindThirteen_of_twelve (h : gfaceWindTwelve_Statement.{u, w, v}) :
    gfaceWindThirteen_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL
  exact gfaceWindThirteen_lobes_of_twelve K
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL)

/-- **`gfaceWindNine_Statement` from the statement with nested wraps.** -/
theorem gfaceWindThirteen_nine_of_statement (h : gfaceWindThirteen_Statement.{u, w, v}) :
    gfaceWindNine_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL
  exact gfaceWindThirteen_arcs_of_lobes K
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL)

/-- **`gfaceWindSix_Statement` from the statement with nested wraps.** -/
theorem gfaceWindThirteen_six_of_statement (h : gfaceWindThirteen_Statement.{u, w, v}) :
    gfaceWindSix_Statement.{u, w, v} :=
  gfaceWindNine_six_of_statement (gfaceWindThirteen_nine_of_statement h)

/-- **The face-set flip statement from the statement with nested wraps.** -/
theorem gfaceWindThirteen_extremal (h : gfaceWindThirteen_Statement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} :=
  gfaceWindNine_extremal (gfaceWindThirteen_nine_of_statement h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindThirteen_wrap_wrap
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindThirteen_Lobes
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindThirteen_arcs_of_lobes
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindThirteen_lobes_of_twelve
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindThirteen_Statement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindThirteen_of_twelve
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindThirteen_nine_of_statement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindThirteen_six_of_statement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindThirteen_extremal
