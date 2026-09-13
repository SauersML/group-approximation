import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the kind transitions of the polygons

Osin (math/0411039v3, §9), proof of Lemma 9.4: "The boundary of `Δ̃_i` decomposes into `k_i`
subpaths, each of which is either `t_j^{±1}` for some `j = 1, …, l`, or an arc".  Proof of
Lemma 9.3: "Clearly the number of arcs of type (A3) is at most 2|M| = 2e ≤ 24n."

`OsinLemma94ClassPolygons` joins consecutive sides of a polygon into classes, the runs of
`exists_cyclicRuns`.  A polygon with at least two classes has at most as many classes as sides
that do not join the next one.  At kind level, two consecutive sides join when both run along one
relator cell.  This module counts the sides that do not.

* `KindJoins P k s`: side `s` of polygon `k` and side `(s + 1) % k_i` have kind `cell j` for one
  `j`.
* `kindNonJoins P k`: the sides `s < k_i` that do not join the next side at kind level.
* `relatorPolygons P`: the polygons with an (A1) side.
* `longTransitions P k`: the kind non-joins where neither side is short.
* `card_kindNonJoins_le`: every kind non-join is short, comes before a short side, or is a long
  transition, so there are at most `2` per short side plus the long transitions.
* `sum_card_kindNonJoins_le_mul`: over `relatorPolygons`, at most `48 ε n` plus the long
  transitions, by `sum_card_shortSides_le_mul`.
* `card_filter_not_le_kindNonJoins_add`: the non-joins of any join predicate are the kind
  non-joins and the same-cell pairs it refuses.
* `OsinLemma94KindTransitionInput`: the kind non-joins number at most `K n`.
* `OsinLemma94LongTransitionInput`: the residual, the long transitions number at most `K n`.
* `osinLemma94KindTransitionInput_of_longTransitions`: the first from the second, with `48 ε + K`.
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
of one relator cell. -/
def KindJoins (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (s : ℕ) : Prop :=
  ∃ j, P.kind k s = .cell j ∧ P.kind k ((s + 1) % P.sideCount k) = .cell j

/-- The sides of polygon `k` that do not join the next side at kind level. -/
noncomputable def kindNonJoins (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (Finset.range (P.sideCount k)).filter fun s => ¬ P.KindJoins k s

/-- The polygons with an (A1) side. -/
noncomputable def relatorPolygons (P : OsinLemma94RealizedPolygons S) : Finset (Fin P.count) :=
  Finset.univ.filter fun k => ∃ s < P.sideCount k, ∃ j, P.kind k s = .cell j

/-- The sides of polygon `k` that are short or come before a short side. -/
noncomputable def shortAdjacent (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (Finset.range (P.sideCount k)).filter fun s =>
    P.kind k s = .short ∨ P.kind k ((s + 1) % P.sideCount k) = .short

/-- **The long transitions of polygon `k`**: the kind non-joins where neither the side nor the
next side is short. -/
noncomputable def longTransitions (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (P.kindNonJoins k).filter fun s =>
    P.kind k s ≠ .short ∧ P.kind k ((s + 1) % P.sideCount k) ≠ .short

/-- A short side and the side before it: at most two sides per short side. -/
theorem card_shortAdjacent_le (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (P.shortAdjacent k).card ≤ 2 * (P.shortSides k).card := by
  have hsub : P.shortAdjacent k ⊆ P.shortSides k ∪
      (P.shortSides k).image fun i => (i + P.sideCount k - 1) % P.sideCount k := by
    intro s hs
    obtain ⟨hs, hshort⟩ := Finset.mem_filter.mp hs
    have hn := Finset.mem_range.mp hs
    rcases hshort with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, h⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(s + 1) % P.sideCount k, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), h⟩, ?_⟩)
      show ((s + 1) % P.sideCount k + P.sideCount k - 1) % P.sideCount k = s
      rcases Nat.lt_or_ge (s + 1) (P.sideCount k) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt, show s + 1 + P.sideCount k - 1 = s + P.sideCount k by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hn]
      · have hlast : P.sideCount k - 1 < P.sideCount k := by omega
        rw [show s + 1 = P.sideCount k by omega, Nat.mod_self, Nat.zero_add,
          Nat.mod_eq_of_lt hlast]
        omega
  calc (P.shortAdjacent k).card
      ≤ (P.shortSides k ∪ (P.shortSides k).image
          fun i => (i + P.sideCount k - 1) % P.sideCount k).card := Finset.card_le_card hsub
    _ ≤ (P.shortSides k).card + ((P.shortSides k).image
          fun i => (i + P.sideCount k - 1) % P.sideCount k).card := Finset.card_union_le _ _
    _ ≤ (P.shortSides k).card + (P.shortSides k).card :=
        Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * (P.shortSides k).card := by ring

/-- **A kind non-join is next to a short side, or it is a long transition.** -/
theorem card_kindNonJoins_le (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (P.kindNonJoins k).card ≤ 2 * (P.shortSides k).card + (P.longTransitions k).card := by
  have hsub : P.kindNonJoins k ⊆ P.shortAdjacent k ∪ P.longTransitions k := by
    intro s hs
    by_cases hshort : P.kind k s = .short ∨ P.kind k ((s + 1) % P.sideCount k) = .short
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, hshort⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, not_or.mp hshort⟩)
  calc (P.kindNonJoins k).card ≤ (P.shortAdjacent k ∪ P.longTransitions k).card :=
        Finset.card_le_card hsub
    _ ≤ (P.shortAdjacent k).card + (P.longTransitions k).card := Finset.card_union_le _ _
    _ ≤ 2 * (P.shortSides k).card + (P.longTransitions k).card :=
        Nat.add_le_add_right (P.card_shortAdjacent_le k) _

/-- **The kind non-joins over the polygons with an (A1) side** number at most `48 ε n` plus the
long transitions, when `|M| ≤ 3 (n + r - 1)` with `n ≥ 1` relator cells. -/
theorem sum_card_kindNonJoins_le_mul (P : OsinLemma94RealizedPolygons S)
    (hcells : 0 < Delta.rCellCount)
    (hcard : S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)) :
    ∑ k ∈ P.relatorPolygons, (P.kindNonJoins k).card ≤
      48 * eps * Delta.rCellCount + ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card := by
  have hshort : ∑ k ∈ P.relatorPolygons, (P.shortSides k).card ≤
      24 * eps * Delta.rCellCount :=
    (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans
      (P.sum_card_shortSides_le_mul hcells hcard)
  calc ∑ k ∈ P.relatorPolygons, (P.kindNonJoins k).card
      ≤ ∑ k ∈ P.relatorPolygons, (2 * (P.shortSides k).card + (P.longTransitions k).card) :=
        Finset.sum_le_sum fun k _ => P.card_kindNonJoins_le k
    _ = 2 * ∑ k ∈ P.relatorPolygons, (P.shortSides k).card +
          ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 48 * eps * Delta.rCellCount + ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card := by
        refine Nat.add_le_add_right ?_ _
        calc 2 * ∑ k ∈ P.relatorPolygons, (P.shortSides k).card
            ≤ 2 * (24 * eps * Delta.rCellCount) := Nat.mul_le_mul_left 2 hshort
          _ = 48 * eps * Delta.rCellCount := by ring

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
globally distinguished section family with `|M| ≤ 3 (n + r - 1)` has at most `K n` kind non-joins
over its polygons with an (A1) side.  The hypotheses are those of `OsinLemma94ClassCountInput`. -/
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
                    ∑ k ∈ P.relatorPolygons, (P.kindNonJoins k).card ≤ K * Delta.rCellCount

/-- **The long transitions, the residual input.**  The hypotheses and quantifiers are those of
`OsinLemma94KindTransitionInput`; the conclusion counts only the long transitions.

Model tests.
* Two relator cells meeting at `m` points bound `m - 1` bubble faces, each with a long
  transition between the arcs of the two cells.  An unpinched bubble is a disc contiguity, so
  `|M| ≤ 3 (n + r - 1)` bounds the unpinched bubbles.
* A bubble pinched on one side around a `G`-face or a hair is not a contiguity, and with the
  `G`-face it is not a `FaceSetBoundary`, so no hypothesis above bounds such bubbles at `n = 2`.
  Splitting the pinch vertex and adding a value-one edge, after opening a hair into a two-gon,
  gives an O-equivalent diagram where the bubble and the `G`-face form a contiguity along the
  arc of the first cell.  The Prop holds on this model only through `weight_maximal`, and a proof
  needs that un-pinch surgery. -/
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

/-- **The kind transitions from the long transitions**, with constant `48 ε + K`: the short
part is `sum_card_kindNonJoins_le_mul`. -/
theorem osinLemma94KindTransitionInput_of_longTransitions
    (h : OsinLemma94LongTransitionInput.{u, w, v}) :
    OsinLemma94KindTransitionInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨K, rho0, hrho0, hK⟩ := heps0 eps heps
  refine ⟨48 * eps + K, rho0, hrho0, fun rho hrho W hW Delta cuts hleast hcells hbelow S hcard
    hminimal P hmax => ?_⟩
  calc ∑ k ∈ P.relatorPolygons, (P.kindNonJoins k).card
      ≤ 48 * eps * Delta.rCellCount + ∑ k ∈ P.relatorPolygons, (P.longTransitions k).card :=
        P.sum_card_kindNonJoins_le_mul hcells hcard
    _ ≤ 48 * eps * Delta.rCellCount + K * Delta.rCellCount :=
        Nat.add_le_add_left
          (hK rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax) _
    _ = (48 * eps + K) * Delta.rCellCount := by ring

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_shortAdjacent_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_kindNonJoins_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.sum_card_kindNonJoins_le_mul
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_filter_not_le_kindNonJoins_add
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94KindTransitionInput_of_longTransitions
