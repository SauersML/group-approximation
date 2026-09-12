# Lane fff-periodic — report

Non-MF verbatim formalization swarm, 2026-09-12.  Clone nm-c.

## Scope: surgery 3 of Osin's Lemma 9.4, Case 2

Osin (arXiv:math/0411039v3, §9), Lemma 9.4, Case 2 splits a vertex of a disc diagram at a pinch
between two complementary G-faces.  A realized section family whose regions avoid both pinch faces
survives the split with the same weight, the same number of regions, the same unbound darts on
every relator cell, and legal labels.  A distinguished family stays distinguished.  Five modules,
all compiled:

| module | last landing | evidence |
|---|---|---|
| `GGT/VanKampen/SurgeryPinchSplitMap` | 33bae46eb | compiled at base 44c6bab14 (imported by Sections) |
| `GGT/VanKampen/SurgeryPinchSplitDiagram` | 0c40dd430 | compiled at base 44c6bab14 (imported by Sections) |
| `GGT/VanKampen/SurgeryPinchSplitRegions` | a6fb37e10 | probes 0912-092950-86238 and 0912-093903-22668, COMPILED (cache restore) |
| `GGT/VanKampen/SurgeryPinchSplitSections` | 556c54a9c | probe 0912-092950-86238, BUILT; 0912-093903-22668, COMPILED |
| `GGT/VanKampen/SurgeryPinchSplitExtremal` | c48fbb6c7 | probe 0912-093903-22668, BUILT |

Probe 0912-092950-86238: base 44c6bab14, 5010 jobs, `PROBE GREEN`.  Probe 0912-093903-22668: base
c48fbb6c7, 5011 jobs, `PROBE GREEN`; a normal land of Extremal then reports `NOTHING TO LAND`.  Every
audited declaration depends on `[propext, Classical.choice, Quot.sound]` only.  The earlier probe
0912-003931-85645 was red only on the unbound-dart block of Sections; 556c54a9c rewrote it.

Wiring: the lead's next root-wiring wave takes `SurgeryPinchSplitSections` (with Regions) at the green
bytes.  Edits to those two land `NM_ATTIC` until a probe is green, never `NM_UNVERIFIED`.  Extremal is
still an orphan.

## Statements

Namespace `GroupApproximation.GGT.VanKampen.PinchSplit`.  Inside `Input`:
`{Delta : DiscDiagram.{u, w, v} W} [DecidableEq Delta.toCombMap.Dart] (I : Input Delta)
{D : RelGenSet G Lambda} {eps : ℕ}`.

Regions (`SurgeryPinchSplitRegions`):

* `abbrev Input.Avoids (s : Finset Delta.toCombMap.Face) : Prop := I.leftFace ∉ s ∧ I.rightFace ∉ s`
* `noncomputable abbrev Input.faceSet (s : Finset Delta.toCombMap.Face) :
  Finset I.diagram.toCombMap.Face := s.image I.kept`
* `Input.merged_not_mem_faceSet {s} (hs : I.Avoids s) : I.merged ∉ I.faceSet s`
* `Input.faceSet_disjoint_iff (_hs : I.Avoids s) (ht : I.Avoids t) :
  Disjoint (I.faceSet s) (I.faceSet t) ↔ Disjoint s t`
* `Input.faceSet_inj (hs : I.Avoids s) (ht : I.Avoids t) (h : I.faceSet s = I.faceSet t) : s = t`
* `noncomputable def Input.transportBoundary {s} (hs : I.Avoids s) (B : FaceSetBoundary Delta s) :
  FaceSetBoundary I.diagram (I.faceSet s)`, with
  `@[simp] Input.transportBoundary_cycle : (I.transportBoundary hs B).cycle = B.cycle`
* `noncomputable def Input.regionCandidate (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) :
  RegionCandidate D eps I.diagram := ⟨I.faceSet a.val.1, I.contiguityGeometry a.property a.val.2⟩`
* `noncomputable def Input.regionFamily (family : Finset (RegionCandidate D eps Delta))
  (havoid : ∀ a ∈ family, I.Avoids a.1) : Finset (RegionCandidate D eps I.diagram)`
* `Input.regionFamily_card : (I.regionFamily family havoid).card = family.card`
* `Input.regionFamily_weight : EstimatingSelection.familyWeight RegionCandidate.weight
  (I.regionFamily family havoid) = EstimatingSelection.familyWeight RegionCandidate.weight family`
* `Input.regionFamily_pairwise (hcompat : EstimatingSelection.PairwiseCompatible
  RegionCandidate.Compatible family) : EstimatingSelection.PairwiseCompatible
  RegionCandidate.Compatible (I.regionFamily family havoid)`
* `Input.regionFamily_faces (ha : a ∈ I.regionFamily family havoid) : ∃ b ∈ family, a.1 = b.1.image I.kept`
* `Input.regionFamily_avoid_merged : ∀ a ∈ I.regionFamily family havoid, I.merged ∉ a.1`

Sections (`SurgeryPinchSplitSections`):

* `Input.regionFamily_profile (ha : a ∈ I.regionFamily family havoid) :
  ∃ b ∈ family, RegionCandidate.SameTargetProfile a b`
* `Input.cellArcDarts_regionCandidate a i :
  (I.regionCandidate a).cellArcDarts (I.cellMap.indexEquiv i) = a.val.cellArcDarts i`
* `Input.boundDarts_regionFamily family havoid interior i :
  RegionCandidate.boundDarts (I.regionFamily family havoid) interior (I.cellMap.indexEquiv i) =
    RegionCandidate.boundDarts family interior i`
* `Input.unboundDarts_eq family havoid i :
  RegionCandidate.unboundDarts (I.regionFamily family havoid) (I.cellMap.indexEquiv i) =
    RegionCandidate.unboundDarts family i`
* `Input.unboundDarts_card`: the card form of `unboundDarts_eq`
* `Input.sum_unboundDarts_card family havoid :
  ∑ j : Fin I.diagram.rCellCount, (RegionCandidate.unboundDarts (I.regionFamily family havoid) j).card =
    ∑ i : Fin Delta.rCellCount, (RegionCandidate.unboundDarts family i).card`
* generic helpers `Input.mem_boundDarts_iff {Xi}`, `Input.mem_unboundDarts_iff {Xi}`,
  `Input.mem_cellArcDarts_iff {Xi}`

Outside `Input`, with `{lambda c : ℝ} {cuts : SectionCuts D lambda c Delta.boundaryWord}`:

* `noncomputable def transportSection (S : RealizedSectionFamily D lambda c eps Delta cuts)
  [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram) (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
  RealizedSectionFamily D lambda c eps Delta cuts`
  (diagram := I.diagram, equiv := S.equiv.trans I.oEquivalent, family := I.regionFamily S.family havoid)
* `transportSection_weight : (transportSection S I havoid).weight = S.weight`
* `transportSection_card : (transportSection S I havoid).family.card = S.family.card`
* `transportSection_labelLegal (E : RelGenSet G Lambda) (h : S.toRealizedRegionFamily.LabelLegal E) :
  (transportSection S I havoid).toRealizedRegionFamily.LabelLegal E`
* `transportSection_diagram : (transportSection S I havoid).diagram = I.diagram` (rfl)
* `transportSection_family : (transportSection S I havoid).family = I.regionFamily S.family havoid` (rfl)

Extremal (`SurgeryPinchSplitExtremal`), with the same outer binders and every declaration taking
`(S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) [DecidableEq S.diagram.toCombMap.Dart]
(I : Input S.diagram) (havoid : ∀ b ∈ S.family, I.Avoids b.1)`:

* `noncomputable def transportDistinguished S I havoid : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts`
  (toRealizedSectionFamily := transportSection S.toRealizedSectionFamily I havoid)
* `transportDistinguished_weight : (transportDistinguished S I havoid).toRealizedSectionFamily.weight =
  S.toRealizedSectionFamily.weight`
* `transportDistinguished_card : (transportDistinguished S I havoid).family.card = S.family.card`
* `transportDistinguished_avoid_merged : ∀ a ∈ (transportDistinguished S I havoid).family, I.merged ∉ a.1`
* `transportDistinguished_toRealizedSectionFamily : (transportDistinguished S I havoid).toRealizedSectionFamily =
  transportSection S.toRealizedSectionFamily I havoid` (rfl)
* `transportDistinguished_diagram : (transportDistinguished S I havoid).diagram = I.diagram` (rfl)
* `transportDistinguished_family : (transportDistinguished S I havoid).family = I.regionFamily S.family havoid` (rfl)

## Why no reverse transport

`GloballyDistinguishedSectionFamily.weight_maximal` and `card_minimal`
(`Estimating/OsinAppendixSections.lean`) compare against every `RealizedSectionFamily D lambda c eps
Delta cuts` with legal labels.  Such a family lives on any reduced diagram O-equivalent to `Delta`,
so the competitors do not depend on which diagram carries the optimum.  The design contract at
lines 89–93 of that file says a surgery that keeps the relator cells and the selected regions yields
another optimum.  `transportSection` keeps the weight, the card and the legal labels, and it stays in
the same class (`equiv := S.equiv.trans I.oEquivalent`).  So `weight_maximal` is
`S.weight_maximal other hother` followed by the weight equation, and `card_minimal` is
`S.card_minimal` read through the card and weight equations.  No map from families on `I.diagram`
back to `Delta` is needed.

## Lean trap

`I.diagram.toCombMap.Dart` is `Delta.toCombMap.Dart` only at default transparency.  A membership
that mixes the two is ill-typed for `rw` and `simp` (instance transparency), and `simp only
[Finset.mem_biUnion]` leaves a `Quot.lift` membership behind.  State membership lemmas at a generic
diagram `{Xi}` and compare across the split in term mode: `Iff.trans`, `and_congr` / `or_congr` /
`not_congr`, `Finset.ext_iff.mp`, and `Iff.of_eq (congrArg (fun l : List I.diagram.toCombMap.Dart =>
d ∈ l) h)`.  `CyclicArc.mapTo_darts _ id _` cannot infer its equation argument; pass it explicitly.

## Residual

* hull-select and dgo-analytic were asked which maximality or minimality statement their waist or
  pocket induction consumes.  No reply had arrived when Extremal landed.  If one of them needs a
  different spelling, it goes in a new declaration in Extremal.
* No census row: these are intermediate carriers in the proof of Lemma 9.4, Case 2, and close no
  manuscript sentence by themselves.
* Spellings sent to hull-select and dgo-analytic (least-area waist) and to the lead.
