import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the kind transitions of the polygons

Osin (math/0411039v3, §9), proof of Lemma 9.4: "The boundary of `Δ̃_i` decomposes into `k_i`
subpaths, each of which is either `t_j^{±1}` for some `j = 1, …, l`, or an arc".  Proof of
Lemma 9.3: "Since unbound arcs of boundaries of R-cells and sections of ∂∆ are separated by
contiguity arcs, the total number of arcs of type (A1) or (A2) in ∆ is not greater than
2|M| + n + r".  "Clearly the number of arcs of type (A3) is at most 2|M| = 2e ≤ 24n."

`OsinLemma94ClassPolygons` joins consecutive sides of a polygon into classes, the runs of
`exists_cyclicRuns`.  A polygon with at least two classes has at most as many classes as sides
that do not join the next one.  At kind level, two consecutive sides join when both run along one
relator cell or both run along one section of `∂Δ`.  This module counts the sides that do not.

* `KindJoins P k s`: side `s` of polygon `k` and side `(s + 1) % k_i` have kind `cell j` for one
  `j`, or kind `boundary j` for one `j`.
* `kindNonJoins P k`: the sides `s < k_i` that do not join the next side at kind level.
* `runEnds P k`: the (A1) and (A2) sides that do not join the next side, the ends of the runs.
* `cuttingSides P k`: the sides of kind `cutting`, from `OsinLemma94CuttingSides`.
* `relatorPolygons P`: the polygons with an (A1) side.
* `longTransitions P k`: the run ends where the next side is not short.
* `card_kindNonJoins_le`: a kind non-join is short, cutting or a run end.
* `card_runEnds_le`: a run end comes before a short side or is a long transition.
* `sum_card_runEnds_le_mul`: over `relatorPolygons`, at most `24 ε n` plus the long transitions,
  by `sum_card_shortSides_le_mul`.
* `card_filter_not_le_kindNonJoins_add`: the non-joins of any join predicate are the kind
  non-joins and the kind joins it refuses.
* `OsinLemma94KindTransitionInput`: the run ends number at most `K n`.
* `OsinLemma94LongTransitionInput`: the residual, the long transitions number at most `K n`.
* `osinLemma94KindTransitionInput_of_longTransitions`: the first from the second, with `24 ε + K`.
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

/-- Side `s` of polygon `k` joins the next side, read cyclically, at kind level: both are arcs
of one relator cell, or both are arcs of one section of `∂Δ`. -/
def KindJoins (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (s : ℕ) : Prop :=
  P.kind k s = P.kind k ((s + 1) % P.sideCount k) ∧
    ((∃ j, P.kind k s = .cell j) ∨ ∃ j, P.kind k s = .boundary j)

/-- The sides of polygon `k` that do not join the next side at kind level. -/
noncomputable def kindNonJoins (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (Finset.range (P.sideCount k)).filter fun s => ¬ P.KindJoins k s

/-- **The run ends of polygon `k`**: the (A1) and (A2) sides that do not join the next side. -/
noncomputable def runEnds (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) : Finset ℕ :=
  (Finset.range (P.sideCount k)).filter fun s =>
    ((∃ j, P.kind k s = .cell j) ∨ ∃ j, P.kind k s = .boundary j) ∧ ¬ P.KindJoins k s

/-- The polygons with an (A1) side. -/
noncomputable def relatorPolygons (P : OsinLemma94RealizedPolygons S) : Finset (Fin P.count) :=
  Finset.univ.filter fun k => ∃ s < P.sideCount k, ∃ j, P.kind k s = .cell j

/-- **The long transitions of polygon `k`**: the run ends where the next side is not short. -/
noncomputable def longTransitions (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (P.runEnds k).filter fun s => P.kind k ((s + 1) % P.sideCount k) ≠ .short

/-- One step forward and one step back around a cycle of length `n`. -/
theorem succ_mod_add_sub_one_mod {n s : ℕ} (hs : s < n) : ((s + 1) % n + n - 1) % n = s := by
  rcases Nat.lt_or_ge (s + 1) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt, show s + 1 + n - 1 = s + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hs]
  · have hlast : n - 1 < n := by omega
    rw [show s + 1 = n by omega, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hlast]
    omega

/-- **A kind non-join is short, cutting or a run end.** -/
theorem card_kindNonJoins_le (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (P.kindNonJoins k).card ≤
      (P.shortSides k).card + (P.cuttingSides k).card + (P.runEnds k).card := by
  have hsub : P.kindNonJoins k ⊆ P.shortSides k ∪ P.cuttingSides k ∪ P.runEnds k := by
    intro s hs
    obtain ⟨hr, hnot⟩ := Finset.mem_filter.mp hs
    cases hkind : P.kind k s with
    | cell j =>
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, Or.inl ⟨j, hkind⟩, hnot⟩)
    | boundary j =>
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, Or.inr ⟨j, hkind⟩, hnot⟩)
    | cutting =>
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, hkind⟩))
    | short =>
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, hkind⟩))
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))

/-- **A run end comes before a short side, or it is a long transition.**  The side before a
short side is determined by it, so there is at most one such run end per short side. -/
theorem card_runEnds_le (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (P.runEnds k).card ≤ (P.shortSides k).card + (P.longTransitions k).card := by
  have hsub : P.runEnds k ⊆
      (P.shortSides k).image (fun i => (i + P.sideCount k - 1) % P.sideCount k) ∪
        P.longTransitions k := by
    intro s hs
    have hn := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    by_cases hshort : P.kind k ((s + 1) % P.sideCount k) = .short
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(s + 1) % P.sideCount k,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), hshort⟩,
        succ_mod_add_sub_one_mod hn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, hshort⟩)
  calc (P.runEnds k).card
      ≤ ((P.shortSides k).image (fun i => (i + P.sideCount k - 1) % P.sideCount k) ∪
          P.longTransitions k).card := Finset.card_le_card hsub
    _ ≤ ((P.shortSides k).image (fun i => (i + P.sideCount k - 1) % P.sideCount k)).card +
          (P.longTransitions k).card := Finset.card_union_le _ _
    _ ≤ (P.shortSides k).card + (P.longTransitions k).card :=
        Nat.add_le_add_right Finset.card_image_le _

/-- **The run ends over the polygons with an (A1) side** number at most `24 ε n` plus the long
transitions, when `|M| ≤ 3 (n + r - 1)` with `n ≥ 1` relator cells. -/
theorem sum_card_runEnds_le_mul (P : OsinLemma94RealizedPolygons S)
    (hcells : 0 < Delta.rCellCount)
    (hcard : S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)) :
    ∑ k ∈ P.relatorPolygons, (P.runEnds k).card ≤
      24 * eps * Delta.rCellCount + ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card := by
  have hshort : ∑ k ∈ P.relatorPolygons, (P.shortSides k).card ≤
      24 * eps * Delta.rCellCount :=
    (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans
      (P.sum_card_shortSides_le_mul hcells hcard)
  calc ∑ k ∈ P.relatorPolygons, (P.runEnds k).card
      ≤ ∑ k ∈ P.relatorPolygons, ((P.shortSides k).card + (P.longTransitions k).card) :=
        Finset.sum_le_sum fun k _ => P.card_runEnds_le k
    _ = ∑ k ∈ P.relatorPolygons, (P.shortSides k).card +
          ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card := Finset.sum_add_distrib
    _ ≤ 24 * eps * Delta.rCellCount + ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card :=
        Nat.add_le_add_right hshort _

/-- **The non-joins of a join predicate.**  The sides that do not satisfy `J` are the kind
non-joins and the sides that join the next one at kind level but do not satisfy `J`. -/
theorem card_filter_not_le_kindNonJoins_add (P : OsinLemma94RealizedPolygons S)
    (k : Fin P.count) (J : ℕ → Prop) [DecidablePred J] :
    ((Finset.range (P.sideCount k)).filter fun s => ¬ J s).card ≤
      (P.kindNonJoins k).card +
        ((Finset.range (P.sideCount k)).filter fun s => P.KindJoins k s ∧ ¬ J s).card := by
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro s hs
  obtain ⟨hr, hnJ⟩ := Finset.mem_filter.mp hs
  by_cases hkind : P.KindJoins k s
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, hkind, hnJ⟩)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, hkind⟩)

end OsinLemma94RealizedPolygons

/-- **The kind transitions of Lemma 9.4.**  There is `ε0` and, for each `ε ≥ ε0`, a constant `K`
and a threshold `ρ0` such that for `ρ ≥ ρ0` every maximal realized polygon family of a dart-minimal
globally distinguished section family with `|M| ≤ 3 (n + r - 1)` has at most `K n` run ends over
its polygons with an (A1) side.  The hypotheses are those of `OsinLemma94ClassCountInput`.

The cutting sides are counted apart, and the short sides by `sum_card_shortSides_le_mul`, so
with `card_kindNonJoins_le` this bounds the kind non-joins. -/
def OsinLemma94KindTransitionInput : Prop :=
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
                    ∑ k ∈ P.relatorPolygons, (P.runEnds k).card ≤ K * Delta.rCellCount

/-- **The long transitions, the residual input.**  The hypotheses and quantifiers are those of
`OsinLemma94KindTransitionInput`; the conclusion counts only the long transitions.

Model tests.
* A pinch of `∂Δ`: a section reads a word of value one, a hair `x x⁻¹` or the boundary of one
  `G`-face, on a closed path at one vertex.  A polygon running along `∂Δ` past that vertex has two
  (A2) sides of one section there.  The boundary word is fixed, and merging the `G`-face into the
  polygon keeps the darts and the weight, so no hypothesis above bounds such pinches; with
  `λ < 1` a section carries a number of them proportional to its length.  These sides join at
  kind level, and they are no transition.
* Two relator cells meeting at `m` points bound `m - 1` bubble faces, each with two long
  transitions between the arcs of the two cells.  An unpinched bubble is a disc contiguity, so
  `|M| ≤ 3 (n + r - 1)` bounds the unpinched bubbles.
* A bubble pinched on one side around a `G`-face or a hair is not a contiguity, and with the
  `G`-face it is not a `FaceSetBoundary`, so no hypothesis above bounds such bubbles at `n = 2`.
  Splitting the pinch vertex and adding a value-one edge, after opening a hair into a two-gon,
  gives an O-equivalent diagram where the bubble and the `G`-face form a contiguity along the
  arc of the first cell.  The Prop holds on this model only through `weight_maximal`, and a proof
  needs that un-pinch surgery.
* A hair on a relator cell inside a polygon ends a run of that cell before a cutting side.  It is
  a pendant path, removed by `pendantPathRemovalInput` against `S.DartMinimal`. -/
def OsinLemma94LongTransitionInput : Prop :=
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
                    ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card ≤
                      K * Delta.rCellCount

/-- **The kind transitions from the long transitions**, with constant `24 ε + K`: the run ends
before a short side are `sum_card_runEnds_le_mul`. -/
theorem osinLemma94KindTransitionInput_of_longTransitions
    (h : OsinLemma94LongTransitionInput.{u, w, v}) :
    OsinLemma94KindTransitionInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨K, rho0, hrho0, hK⟩ := heps0 eps heps
  refine ⟨24 * eps + K, rho0, hrho0, fun rho hrho W hW Delta cuts hleast hcells hbelow S hcard
    hminimal P hmax => ?_⟩
  calc ∑ k ∈ P.relatorPolygons, (P.runEnds k).card
      ≤ 24 * eps * Delta.rCellCount + ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card :=
        P.sum_card_runEnds_le_mul hcells hcard
    _ ≤ 24 * eps * Delta.rCellCount + K * Delta.rCellCount :=
        Nat.add_le_add_left
          (hK rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax) _
    _ = (24 * eps + K) * Delta.rCellCount := by ring

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.succ_mod_add_sub_one_mod
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_kindNonJoins_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_runEnds_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.sum_card_runEnds_le_mul
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_filter_not_le_kindNonJoins_add
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94KindTransitionInput_of_longTransitions
