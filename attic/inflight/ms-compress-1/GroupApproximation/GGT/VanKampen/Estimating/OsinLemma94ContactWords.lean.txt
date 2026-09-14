import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: object changes and section corners

A contact transition of polygon `k` at side `s` ends a run along one object and starts a run
along another side of cell or boundary kind.  Either both sides run along `∂Δ` in different
sections, a *section corner*, or the two objects across differ, an *object change*.

* `BoundaryPair`, `sectionCorners`, `objectChanges`.
* `card_contactTransitions_le`: the contact transitions are the object changes and the section
  corners.
* `objectChanges_eq_empty_of_card_le_one`: a polygon with at most one neighbour has no object
  change, since an object change reads two different neighbours.
* `OsinLemma94ObjectChangesStatement`: a rich polygon has at most `2 d_k` object changes.  This is
  the target of the side-word translation: the objects read along the walk, with runs merged, have
  no equal neighbours and no `a b a b` (`neighbourFacesNoninterleaving`), so
  `ListNoABAB.length_add_one_le_two_mul_card` applies.
* `OsinLemma94SectionCornersInput`: the section corners over the polygons with an (A1) side number
  at most `K n`.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- Side `s` and the next side both run along `∂Δ`. -/
def BoundaryPair (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (s : ℕ) : Prop :=
  (∃ j, P.kind k s = .boundary j) ∧ ∃ j, P.kind k ((s + 1) % P.sideCount k) = .boundary j

/-- **The section corners of polygon `k`**: contact transitions between two boundary sides. -/
noncomputable def sectionCorners (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (P.contactTransitions k).filter fun s => P.BoundaryPair k s

/-- **The object changes of polygon `k`**: the other contact transitions. -/
noncomputable def objectChanges (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (P.contactTransitions k).filter fun s => ¬ P.BoundaryPair k s

theorem card_contactTransitions_le (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (P.contactTransitions k).card ≤ (P.objectChanges k).card + (P.sectionCorners k).card := by
  have hsub : P.contactTransitions k ⊆ P.objectChanges k ∪ P.sectionCorners k := by
    intro s hs
    by_cases h : P.BoundaryPair k s
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, h⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- An object change reads two different neighbours. -/
theorem exists_two_neighbours_of_mem_objectChanges (P : OsinLemma94RealizedPolygons S)
    {k : Fin P.count} {s : ℕ} (hs : s ∈ P.objectChanges k) :
    ∃ o ∈ P.neighbours k, ∃ o' ∈ P.neighbours k, o ≠ o' := by
  obtain ⟨hcont, hnb⟩ := Finset.mem_filter.mp hs
  have hlong : s ∈ P.longTransitions k := (Finset.mem_filter.mp hcont).1
  have hrun : s ∈ P.runEnds k := (Finset.mem_filter.mp hlong).1
  obtain ⟨hrange, hkind, -⟩ := Finset.mem_filter.mp hrun
  have hslt : s < P.sideCount k := Finset.mem_range.mp hrange
  have hnlt : (s + 1) % P.sideCount k < P.sideCount k := Nat.mod_lt _ (by omega)
  have hne := P.kind_ne_next_of_mem_longTransitions hlong
  have hnext := P.next_kind_of_mem_contactTransitions hcont
  have hmem : ∀ i, i < P.sideCount k → ∀ o, sideObject (P.kind k i) = some o →
      o ∈ P.neighbours k := fun i hi o ho => (P.mem_neighbours k o).mpr ⟨i, hi, ho⟩
  cases hk : P.kind k s with
  | cell j =>
    cases hn : P.kind k ((s + 1) % P.sideCount k) with
    | cell j' =>
      refine ⟨some j, hmem s hslt _ (by rw [hk]; rfl), some j', hmem _ hnlt _ (by rw [hn]; rfl),
        fun h => hne ?_⟩
      rw [hk, hn, Option.some_injective _ h]
    | boundary j' =>
      exact ⟨some j, hmem s hslt _ (by rw [hk]; rfl), none, hmem _ hnlt _ (by rw [hn]; rfl),
        by simp⟩
    | cutting => rw [hn] at hnext; simp at hnext
    | short => rw [hn] at hnext; simp at hnext
  | boundary j =>
    cases hn : P.kind k ((s + 1) % P.sideCount k) with
    | cell j' =>
      exact ⟨none, hmem s hslt _ (by rw [hk]; rfl), some j', hmem _ hnlt _ (by rw [hn]; rfl),
        by simp⟩
    | boundary j' => exact absurd ⟨⟨j, hk⟩, ⟨j', hn⟩⟩ hnb
    | cutting => rw [hn] at hnext; simp at hnext
    | short => rw [hn] at hnext; simp at hnext
  | cutting => rw [hk] at hkind; simp at hkind
  | short => rw [hk] at hkind; simp at hkind

/-- **A polygon with at most one neighbour has no object change.** -/
theorem objectChanges_eq_empty_of_card_le_one (P : OsinLemma94RealizedPolygons S)
    (k : Fin P.count) (hk : (P.neighbours k).card ≤ 1) : P.objectChanges k = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
  obtain ⟨o, ho, o', ho', hoo'⟩ := P.exists_two_neighbours_of_mem_objectChanges hs
  have : 1 < (P.neighbours k).card := Finset.one_lt_card.mpr ⟨o, ho, o', ho', hoo'⟩
  omega

end OsinLemma94RealizedPolygons

/-- **The object changes of a rich polygon.**  A polygon with at least two neighbours has at most
`2 d_k` object changes.

Model tests (hand).
* A polygon reading cells `a`, `b`, `a`, `c` in order has four object changes and `d = 3`:
  `4 ≤ 6`.
* A polygon reading `a`, `b`, `a`, `b` would have four changes with `d = 2`, `4 ≤ 4`, so the bound
  holds even there; the interleaving is excluded on planar maps by
  `neighbourFacesNoninterleaving`, which the translation uses for the sharper word bound. -/
def OsinLemma94ObjectChangesStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count), P.Rich k →
      (P.objectChanges k).card ≤ 2 * (P.neighbours k).card

/-- **The section corners of Lemma 9.4.**  Under the binders of `OsinLemma94LongTransitionInput`,
the section corners over the polygons with an (A1) side number at most `K n`.

Model tests (hand).
* One section (`r = 1`): no two boundary sides of different sections exist, so the sum is zero.
* A polygon running along `∂Δ` across the cut between sections `j` and `j + 1`, with a vertex of
  degree two at the cut: one section corner at that cut.  Each of the `r ≤ 4` cut positions of the
  outer walk is one vertex corner of the exterior, and a corner of the exterior belongs to one
  polygon walk, so a bound `2 r ≤ 8 ≤ 8 n` is expected. -/
def OsinLemma94SectionCornersInput : Prop :=
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
                    ∑ k ∈ P.relatorPolygons, (P.sectionCorners k).card ≤ K * Delta.rCellCount

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_contactTransitions_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.exists_two_neighbours_of_mem_objectChanges
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.objectChanges_eq_empty_of_card_le_one
