import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassTransitions
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the long transitions, split by the next side

`OsinLemma94LongTransitionInput` (`OsinLemma94ClassTransitions.lean`) bounds the long transitions
of the polygons with an (A1) side: the run ends whose next side is not short.  Their next side is
of kind `cell`, `boundary` or `cutting`, and the two cases need different arguments.

* A **contact transition** ends a run along one relator cell or section of `∂Δ` where the walk
  starts a run along another one.  At the corner the rotation reads the first object, the polygon
  and the second object, so it is a contact of two distinct objects around the polygon.  Euler's
  count on the planar graph of the objects bounds the contacts once no two-gon of that graph is
  empty.  An empty two-gon is a bubble between two objects.
  - Unpinched, it is a singleton contiguity region, against `weight_maximal`
    (`GloballyDistinguishedSectionFamily.false_of_avoided_singleton`).
  - Pinched, it is absorbed after splitting the pinch (`PinchSplit.pinchSplitAbsorption`).
* A **cutting transition** ends a run where the walk enters a cutting path.  A dart-minimal family
  has no pendant cutting tree, so the cutting paths join boundary components of the polygon, and an
  entry marks a hole that contains an object.

This module proves the split and states the two counts as named pieces.

* `contactTransitions`, `cuttingTransitions`: the long transitions whose next side is not, or is,
  cutting.
* `kind_ne_next_of_mem_longTransitions`: a long transition changes the kind.
* `next_kind_of_mem_contactTransitions`: the next side of a contact transition is a cell or
  boundary side.
* `card_longTransitions_le`, `sum_card_longTransitions_le`: the long transitions are the contact
  and the cutting transitions.
* `OsinLemma94ContactTransitionInput`, `OsinLemma94CuttingTransitionInput`: the two counts, under
  the binders of `OsinLemma94LongTransitionInput`.
* `osinLemma94LongTransitionInput_of_pieces`: the long transitions from the two counts, with
  constant `K₁ + K₂`.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.4, arXiv:math/0411039v3, §9); certifies no
printed sentence on its own.  The theorem here is a reduction, not a discharge: both pieces are
open.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open scoped Classical

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **The contact transitions of polygon `k`**: the long transitions whose next side is a cell or
boundary side. -/
noncomputable def contactTransitions (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (P.longTransitions k).filter fun s => P.kind k ((s + 1) % P.sideCount k) ≠ .cutting

/-- **The cutting transitions of polygon `k`**: the long transitions whose next side is a cutting
side. -/
noncomputable def cuttingTransitions (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (P.longTransitions k).filter fun s => P.kind k ((s + 1) % P.sideCount k) = .cutting

/-- A long transition changes the kind of the side. -/
theorem kind_ne_next_of_mem_longTransitions (P : OsinLemma94RealizedPolygons S)
    {k : Fin P.count} {s : ℕ} (hs : s ∈ P.longTransitions k) :
    P.kind k s ≠ P.kind k ((s + 1) % P.sideCount k) := by
  obtain ⟨hrun, -⟩ := Finset.mem_filter.mp hs
  obtain ⟨-, hkind, hnot⟩ := Finset.mem_filter.mp hrun
  exact fun heq => hnot ⟨heq, hkind⟩

/-- The next side of a contact transition is a cell side or a boundary side. -/
theorem next_kind_of_mem_contactTransitions (P : OsinLemma94RealizedPolygons S)
    {k : Fin P.count} {s : ℕ} (hs : s ∈ P.contactTransitions k) :
    (∃ j, P.kind k ((s + 1) % P.sideCount k) = .cell j) ∨
      ∃ j, P.kind k ((s + 1) % P.sideCount k) = .boundary j := by
  obtain ⟨hlong, hncut⟩ := Finset.mem_filter.mp hs
  have hnshort := (Finset.mem_filter.mp hlong).2
  cases h : P.kind k ((s + 1) % P.sideCount k) with
  | cell j => exact Or.inl ⟨j, rfl⟩
  | boundary j => exact Or.inr ⟨j, rfl⟩
  | cutting => exact absurd h hncut
  | short => exact absurd h hnshort

/-- **The long transitions are the contact and the cutting transitions.** -/
theorem card_longTransitions_le (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (P.longTransitions k).card ≤
      (P.contactTransitions k).card + (P.cuttingTransitions k).card := by
  have hsub : P.longTransitions k ⊆ P.contactTransitions k ∪ P.cuttingTransitions k := by
    intro s hs
    by_cases hcut : P.kind k ((s + 1) % P.sideCount k) = .cutting
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, hcut⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, hcut⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Summed over the polygons with an (A1) side. -/
theorem sum_card_longTransitions_le (P : OsinLemma94RealizedPolygons S) :
    ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card ≤
      ∑ k ∈ P.relatorPolygons, (P.contactTransitions k).card +
        ∑ k ∈ P.relatorPolygons, (P.cuttingTransitions k).card := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => P.card_longTransitions_le k

/-- **Model test**: a family with no polygons has no polygon with an (A1) side, so both counts
vanish and every constant works.  This is the calibration case only. -/
theorem relatorPolygons_eq_empty_of_count_eq_zero (P : OsinLemma94RealizedPolygons S)
    (h : P.count = 0) : P.relatorPolygons = ∅ := by
  ext k
  exfalso
  have hk := k.2
  omega

end OsinLemma94RealizedPolygons

/-- **The contact transitions of Lemma 9.4.**  Under the binders of
`OsinLemma94LongTransitionInput`, the contact transitions over the polygons with an (A1) side
number at most `K n`.

Model tests.
* No polygons: the sum is empty (`relatorPolygons_eq_empty_of_count_eq_zero`).
* Two relator cells meeting at `m` points bound `m - 1` bubbles, each a polygon with two contact
  transitions.  On a globally distinguished family an unpinched bubble with two nonempty arcs is a
  singleton contiguity region that no region contains, so `false_of_avoided_singleton` excludes it.
  A bubble pinched around a `G`-face is merged by the split of the pinch, and
  `PinchSplit.pinchSplitAbsorption` excludes it when the merged face reads as a region.  Without
  these exclusions the model gives `2 (m - 1)` contacts at `n = 2`, so the Prop holds on the model
  only through `weight_maximal`.
* Three cells around a polygon, pairwise touching: three contacts at a face of degree three of the
  object graph, as Euler's count allows. -/
def OsinLemma94ContactTransitionInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ K : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∑ k ∈ P.relatorPolygons, (P.contactTransitions k).card ≤
                      K * Delta.rCellCount

/-- **The cutting transitions of Lemma 9.4.**  Under the binders of
`OsinLemma94LongTransitionInput`, the cutting transitions over the polygons with an (A1) side
number at most `K n`.

Model tests.
* No polygons: the sum is empty.
* A polygon surrounding one relator cell, joined to a section of `∂Δ` by one bridge, reads a
  boundary side, the bridge, the whole cell arc, and the bridge back: two cutting transitions.
  The bridge exists because the polygon is an annulus.  Its hole holds the cell, so the count is at
  most twice the number of holes, and every hole holds an object.
* A pendant cutting path inside the polygon would end a run before a cutting side with no hole.  A
  dart-minimal family has none: deleting it removes darts and keeps the unbound sum
  (`OsinLemma94CuttingSides.lean`, the leaf argument). -/
def OsinLemma94CuttingTransitionInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ K : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∑ k ∈ P.relatorPolygons, (P.cuttingTransitions k).card ≤
                      K * Delta.rCellCount

/-- **The long transitions from the contact and the cutting transitions**, with constant
`K₁ + K₂`, threshold `max ε₁ ε₂` and `ρ₀ = max ρ₁ ρ₂`. -/
theorem osinLemma94LongTransitionInput_of_pieces
    (hcontact : OsinLemma94ContactTransitionInput.{u, w, v})
    (hcutting : OsinLemma94CuttingTransitionInput.{u, w, v}) :
    OsinLemma94LongTransitionInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e1, h1⟩ := hcontact D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e2, h2⟩ := hcutting D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max e1 e2, fun eps heps => ?_⟩
  obtain ⟨K1, r1, hr1, hK1⟩ := h1 eps ((le_max_left _ _).trans heps)
  obtain ⟨K2, r2, _, hK2⟩ := h2 eps ((le_max_right _ _).trans heps)
  refine ⟨K1 + K2, max r1 r2, lt_of_lt_of_le hr1 (le_max_left _ _),
    fun rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax => ?_⟩
  calc ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card
      ≤ ∑ k ∈ P.relatorPolygons, (P.contactTransitions k).card +
          ∑ k ∈ P.relatorPolygons, (P.cuttingTransitions k).card :=
        P.sum_card_longTransitions_le
    _ ≤ K1 * Delta.rCellCount + K2 * Delta.rCellCount :=
        Nat.add_le_add
          (hK1 rho ((le_max_left _ _).trans hrho) W hW Delta cuts hleast hcells hbelow S hcard
            hminimal P hmax)
          (hK2 rho ((le_max_right _ _).trans hrho) W hW Delta cuts hleast hcells hbelow S hcard
            hminimal P hmax)
    _ = (K1 + K2) * Delta.rCellCount := by ring

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.kind_ne_next_of_mem_longTransitions
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.next_kind_of_mem_contactTransitions
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_longTransitions_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.sum_card_longTransitions_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.relatorPolygons_eq_empty_of_count_eq_zero
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94LongTransitionInput_of_pieces
