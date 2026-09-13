# hull-count94

## Scope
- Item (lead, after the 08:30 restart): the PolygonCount piece of
  `osinLemma94Section_of_planarPieces`. That is `OsinLemma94PolygonCountInput` in
  `Estimating/OsinLemma94PlanarPieces.lean` (hull-unbound).
- Roster split (ROSTER l.1080-1087):
  - this lane writes the producer of `OsinLemma94ClassPolygons` and the
    `OsinLemma94ClassCountInput` assembly;
  - audit-intro landed `exists_cyclicRuns` (`OsinLemma94ClassRuns`, 25aef6af9);
  - sec5-sentences writes the kind-level transition count;
  - hull-component writes the bubble accounting (`OsinLemma94ClassCovers`, 13cf15e1a).
- Helper: audit-intro, now on the face-arc fit lemmas for the producer's `cell_arc`.

## Covers half: conditional, not closed
- `osinLemma94PolygonCoversInput` (`Estimating/OsinLemma94PolygonCount.lean`) takes
  `hsame : OsinLemma94UnboundSameCellStatement`. That statement is false in general (ROSTER
  l.1046-1047): per run only `|T_R| ≤ ((1 − λ) N_R + c) / λ`.
- The class route replaces the side-level Covers half, through `ClassCovers M L` with a factor `M`.
- These still stand and are used (`Estimating/OsinLemma94PolygonCovers.lean`, probe
  0913-093648-12289 GREEN):
  - `OsinCCondition.listVal_ne_one_of_mem`;
  - `GloballyDistinguishedSectionFamily.alpha_faceOf_not_cell_of_unbound`;
  - `OsinLemma94RealizedPolygons.exists_relatorSide_of_unbound`;
  - `covers_of_regionFacing_le`.

## F1 quantifier order: done
- `∃ K` comes after `∀ ε` in `OsinLemma94AntiparallelMetricStatement`, `OsinLemma94PolygonCountInput`
  and `OsinLemma94PolygonSideBudgetInput`. Probe 0913-115846-46341 GREEN.

## Stage B: class polygons (ROSTER l.783-786, l.893-898, l.1080-1098)
- `Estimating/OsinLemma94PolygonClasses.lean` (this lane): 6db79cea7, then a25fe2383 (probe
  0913-152533-28063 GREEN, axioms within propext, Classical.choice, Quot.sound).
  - `OsinLemma94ClassPolygons P`: the sides of each polygon, read cyclically from `classBase`, split
    into classes. The class darts are `(classSides k i).flatMap fun s => P.sideDarts k s ++ gap k s`.
    - A class of kind `cell j` is one reversed arc of cell `j`, gaps included. A class of kind
      `boundary j` is one arc of section `j`.
    - Gaps have value one, and the last gap of a class is empty.
    - Cutting and short classes are single sides.
  - `ClassBudget K : ∑ k ∈ budgetPolygons, classCount k ≤ K n`.
  - `ClassCovers M L : S ≤ M ∑ k, classWordLength (word k) (classCount k) (relatorClasses k) + L n`
    (a25fe2383).
    - Why the factor: fff-periodic's site 5 count (T) bounds a same-cell unbound stretch only by
      `⌈1/λ⌉₊` times the other unbound darts, so no fixed `L` is enough.
    - hull-unbound's Q2 factor `1 + ⌈(c + 2)/λ⌉₊` for gap-free words also enters here.
  - Proved:
    - `corner_closed`;
    - `short_of_not_mem`;
    - `dense_of_classCovers`, with density `⌊ρ / (4 M²)⌋`;
    - `unbound_lt_of_classes`, which takes `0 < M`, `4 M² ρₘ ≤ ρ` and `4 L² ≤ ρ`, through
      hull-component's `exists_of_budget_on`;
    - `ofSides`, the model test with every side its own class.
- Rule 22 miss:
  - hull-component's `OsinLemma94ClassCovers` (13cf15e1a) landed after my user grep. It spells
    `Q.ClassCovers (24 * eps + 2 * (K + 24) * B + T)`, so it is red against a25fe2383.
  - Fix: `Q.ClassCovers 1 (…)`. Sent to hull-component and main.
- S5 window: theoremc-retire's hold (15:34) names this lane. a25fe2383 went in the same minute.
  Their replay needs the a25fe2383 bytes. This lane lands no Lean module until the window closes.

## Producer (next module: `Estimating/OsinLemma94ClassJoins.lean`)
- Planarity-free, over `exists_cyclicRuns`.
- Join predicate `J k s`: sides `s` and `(s + 1) % n` have the same kind `.cell j`, and the junction
  gap has value one with no dart on the face walk.
- Junction gap:
  - the reversed, `α`-mapped chain `facePerm (α e'), …, facePerm^t (α e')`;
  - `e` is the last dart of side `s`, and `e'` is the head of side `s + 1`;
  - `t` is least with `facePerm^(t+1) (α e') = α e`.
- `cell_arc`: the forward class walk is a `facePerm` chain of the cell face.
  - If it is no longer than the face, it is one arc.
  - Otherwise its first dart occurs twice. But it occurs at most once on the sides (the face walk is
    `nodup`) and never on the gaps.
- Budget: `classCount ≤ max 1 #nonJoins`. Non-joins are kind transitions and bad same-cell junctions.
- audit-intro's sub-piece: the fit lemmas (an arc from a short `facePerm` chain, a double count for a
  long one).

## Residual Props
- `OsinLemma94ClassCountInput` (PolygonClasses):
  `∃ ε₀, ∀ ε ≥ ε₀, ∃ K M L, 0 < M ∧ ∃ ρ₀ > 0, ∀ ρ ≥ ρ₀, …`, with clause (b) of Lemma 9.7 below the
  relator cell count as a hypothesis, `…, P.Maximal → ∃ Q, Q.ClassBudget K ∧ Q.ClassCovers M L`.
  It is assembled from:
  - the non-join count over polygons with an (A1) side and at least two non-joins. The owner is
    still to be ruled. Bad same-cell junctions need the loop value lemma and the pocket Jordan step.
  - hull-component's `classCovers_of_endLoops`, with its end-loop bounds;
  - fff-periodic's site 5 count (T) and its pocket binder.
- `OsinLemma94PolygonSideBudgetInput` (PolygonCount). It is superseded once the Case 1 users move to
  class words. Model tests against the side-level budget: pockets (`K` after `ε`), spurs,
  value-one boundary bubbles, pinched relator cells.

## On main from earlier items
- `GGT/OlshanskiiFirstVisit.lean`, `GGT/OlshanskiiOrientedLemma25.lean` (1c5f36398),
  `GGT/OlshanskiiOrientedClasses.lean` (0963dc2b4), `GGT/OlshanskiiOrientedBisection.lean` and
  `GGT/OlshanskiiOrientedThreeClasses.lean` (0ff430236). This is the oriented Lemma 3.7 layer under
  `OsinLemma94AntiparallelMetricStatement` (closed by sec5-sentences, e3da1ba60).
- `OsinLemma94RunInput` and `OsinLemma94Counting` (82ba54dfb) are superseded and have no users.

## Census
- The LINE:1636 row (thm:hull, Osin Lemma 9.4 inside Hull's proof) stays partial. Rows: side budget
  (4e7a84555), class polygons (6db79cea7), respelled count (a25fe2383).

## Next
1. hull-component's one-line fix lands. theoremc-retire's S5 window closes.
2. If theoremc-retire's named `OsinLemma97Below` matches the binder, switch `ClassCountInput` to it.
3. Write `OsinLemma94ClassJoins`: junction gaps, runs, `Q`, the budget lemma. Probe it once
   audit-intro's fit lemmas land.
4. The `ClassCountInput` assembly.

## Coordination
- hull-unbound owns `OsinLemma94PlanarPieces`, `OsinLemma94Pieces`, `OsinLemma94GapFreeWords`,
  `OsinUnboundSharedEdge` and `UnboundWordPolygonMonotone`.
- hull-component owns `OsinLemma94BudgetFilter` and `OsinLemma94ClassCovers`.
- audit-intro owns `OsinLemma94RegionSideCount` and `OsinLemma94ClassRuns`.
- sec5-sentences owns `OsinLemma94DartMinimal` and `OsinLemma94AntiparallelMetric`.
- theoremc-retire owns `OsinLemma94CaseOneWalk` and `OsinUnboundCaseOneRun`. ko-closed owns
  `OsinLemma94CaseOneWalkHolds`.
