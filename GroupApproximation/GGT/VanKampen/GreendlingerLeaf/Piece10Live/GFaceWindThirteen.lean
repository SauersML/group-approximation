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
