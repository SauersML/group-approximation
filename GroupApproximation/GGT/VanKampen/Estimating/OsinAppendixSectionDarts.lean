import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionBridge
import GroupApproximation.GGT.VanKampen.Estimating.ShortSection
import GroupApproximation.Meta.AxiomGuard

/-!
# Word-level section cuts as dart-based boundary sections

`SectionCuts` (`Estimating/OsinAppendixSections.lean`) records Osin's boundary
sections `∂Δ = q_1 ⋯ q_r` as positions of the boundary word, so that one record
serves every O-equivalent diagram.  `Estimating/Lemma65Statement.lean` and
`Estimating/ShortSection.lean` state their lemmas for the dart-based
`Embedded.BoundarySections` of one diagram.  This file connects the two.

* `SectionCuts.toBoundarySections`: on any diagram `Ξ` whose boundary word is
  the cut word, the pieces of `outerDarts Ξ` between consecutive cuts are an
  exact concatenation, and each reads a `(λ, c)`-quasi-geodesic section word.
* `RegionCandidate.targetsSection_of_targetsSectionIndex`: a region to section
  `j` in the positional sense targets that dart piece in the sense of
  `Contiguity.TargetsSection`.
* `RegionCandidate.sourceArc_length_le_of_shortSection`: Osin's side-arc
  estimate for a region to a short section, `l(u) ≤ λ⁻¹ (3ε + c)`, obtained from
  `Contiguity.sourceArc_length_le_of_boundarySection`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-! ## Cutting a list at monotone positions -/

namespace SectionCuts

/-- Concatenating the pieces of a list between monotone cut positions recovers
the prefix up to the last cut. -/
theorem flatten_ofFn_pieces {α : Type*} (l : List α) :
    ∀ (n : ℕ) (cut : Fin (n + 1) → ℕ), cut 0 = 0 → Monotone cut →
      (List.ofFn fun j : Fin n =>
          (l.drop (cut j.castSucc)).take (cut j.succ - cut j.castSucc)).flatten =
        l.take (cut (Fin.last n)) := by
  intro n
  induction n with
  | zero =>
      intro cut h0 _
      simp [h0]
  | succ n ih =>
      intro cut h0 hmono
      have hih : (List.ofFn fun j : Fin n =>
          (l.drop (cut j.castSucc.castSucc)).take
            (cut j.succ.castSucc - cut j.castSucc.castSucc)).flatten =
          l.take (cut (Fin.last n).castSucc) :=
        ih (fun i => cut i.castSucc) h0
          (fun a b hab => hmono (show a.castSucc ≤ b.castSucc from hab))
      simp only [List.ofFn_succ_last, List.flatten_append, List.flatten_singleton,
        Fin.succ_castSucc, Fin.succ_last, Nat.succ_eq_add_one]
      rw [hih, ← List.take_add,
        Nat.add_sub_cancel' (hmono (Fin.le_last (Fin.last n).castSucc))]

/-- The word on a piece of the outer darts is the same piece of the boundary
word. -/
theorem dartWord_outerDarts_drop_take {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (Xi : DiscDiagram.{u, w, v} W) (a b : ℕ) :
    dartWord Xi (((outerDarts Xi).drop a).take b) = (Xi.boundaryWord.drop a).take b := by
  rw [← dartWord_outerDarts Xi]
  simp only [dartWord, List.map_drop, List.map_take]

/-- **The dart-based sections** of a diagram whose boundary word is the cut
word. -/
def toBoundarySections {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {word : List (RelLetter G Lambda)}
    (cuts : SectionCuts D lambda c word) (Xi : DiscDiagram.{u, w, v} W)
    (hword : Xi.boundaryWord = word) : BoundarySections D lambda c Xi where
  count := cuts.count
  count_pos := cuts.count_pos
  count_le := cuts.count_le
  part := fun j =>
    ((outerDarts Xi).drop (cuts.cut j.castSucc)).take
      (cuts.cut j.succ - cuts.cut j.castSucc)
  decomposition := by
    have hlen : (outerDarts Xi).length = word.length := by
      rw [← hword, ← dartWord_outerDarts Xi, dartWord, List.length_map]
    rw [flatten_ofFn_pieces (outerDarts Xi) cuts.count cuts.cut cuts.cut_zero
      cuts.cut_mono, cuts.cut_last, ← hlen, List.take_length]
  quasiGeodesic := by
    intro j
    show IsLambdaCQuasiGeodesicWord D lambda c
      (dartWord Xi (((outerDarts Xi).drop (cuts.cut j.castSucc)).take
        (cuts.cut j.succ - cuts.cut j.castSucc)))
    rw [dartWord_outerDarts_drop_take, hword]
    exact cuts.quasiGeodesic j

/-- Every cut position is at most the length of the cut word. -/
theorem cut_le_length {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {word : List (RelLetter G Lambda)}
    (cuts : SectionCuts D lambda c word) (k : Fin (cuts.count + 1)) :
    cuts.cut k ≤ word.length := by
  rw [← cuts.cut_last]
  exact cuts.cut_mono (Fin.le_last k)

end SectionCuts

/-! ## Regions to sections, in darts -/

/-- A cyclic arc whose positions lie in `[p, q)` of its carrier lies in the
piece of the carrier between those positions. -/
theorem Embedded.CyclicArc.mem_drop_take_of_le {α : Type*} {cycle : List α}
    (arc : CyclicArc cycle) {p q : ℕ} (hp : p ≤ arc.start.1)
    (hq : arc.start.1 + arc.length ≤ q) (hqlen : q ≤ cycle.length)
    {d : α} (hd : d ∈ arc.darts) : d ∈ (cycle.drop p).take (q - p) := by
  have hlen : arc.length ≤ (cycle.drop arc.start.1).length := by
    rw [List.length_drop]
    omega
  have hd' : d ∈ (cycle.drop arc.start.1).take arc.length := by
    have h := hd
    rwa [CyclicArc.darts, CyclicArc.rotated, List.take_append_of_le_length hlen] at h
  have hdrop : cycle.drop arc.start.1 = (cycle.drop p).drop (arc.start.1 - p) := by
    rw [List.drop_drop, Nat.add_sub_cancel' hp]
  rw [hdrop] at hd'
  have hx : d ∈ (cycle.drop p).take (arc.start.1 - p + arc.length) := by
    rw [List.take_add]
    exact List.mem_append_right _ hd'
  exact (List.take_sublist_take_left (by omega)).subset hx

/-- **A region to section `j`, in darts.**  Its outer arc lies in the `j`-th dart
piece of `toBoundarySections`. -/
theorem Embedded.RegionCandidate.targetsSection_of_targetsSectionIndex
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ}
    {word : List (RelLetter G Lambda)} {Xi : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c word} (hword : Xi.boundaryWord = word)
    {j : Fin cuts.count} (a : RegionCandidate D eps Xi)
    (h : RegionCandidate.TargetsSectionIndex cuts j a) :
    (a.toContiguityOfTargetNone h.1).TargetsSection
      ((cuts.toBoundarySections Xi hword).part j) := by
  refine ⟨h.1, ?_⟩
  intro d hd
  have hT : targetDarts Xi a.2.target = outerDarts Xi := by
    simp only [h.1, targetDarts]
  have hlenOuter : (outerDarts Xi).length = word.length := by
    rw [← hword, ← dartWord_outerDarts Xi, dartWord, List.length_map]
  have hqlen : cuts.cut j.succ ≤ (targetDarts Xi a.2.target).length := by
    rw [hT, hlenOuter]
    exact cuts.cut_le_length j.succ
  have hmem := CyclicArc.mem_drop_take_of_le a.2.targetArc h.2.1 h.2.2 hqlen hd
  rw [hT] at hmem
  exact hmem

/-- **Osin's side-arc estimate for a region to a short section**: "if `u` is a
contiguity arc of `Π` to `s_1`, then `l(u) ≤ λ⁻¹(3ε + c)` since `u` is
`(λ, c)`-quasi-geodesic and `l(s_1) ≤ ε`." -/
theorem Embedded.RegionCandidate.sourceArc_length_le_of_shortSection
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    {word : List (RelLetter G Lambda)} {Xi : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c word} (hword : Xi.boundaryWord = word)
    {j : Fin cuts.count} (a : RegionCandidate D eps Xi)
    (h : RegionCandidate.TargetsSectionIndex cuts j a)
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hshort : cuts.cut j.succ - cuts.cut j.castSucc ≤ eps) :
    (a.2.sourceArc.length : ℝ) ≤ lambda⁻¹ * (3 * (eps : ℝ) + c) := by
  have hpart : ((cuts.toBoundarySections Xi hword).part j).length ≤ eps := by
    show (((outerDarts Xi).drop (cuts.cut j.castSucc)).take
      (cuts.cut j.succ - cuts.cut j.castSucc)).length ≤ eps
    rw [List.length_take]
    exact le_trans (min_le_left _ _) hshort
  exact (a.toContiguityOfTargetNone h.1).sourceArc_length_le_of_boundarySection
    (cuts.toBoundarySections Xi hword) j hcondition hlambda
    (RegionCandidate.targetsSection_of_targetsSectionIndex hword a h) hpart

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectionCuts.flatten_ofFn_pieces
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.mem_drop_take_of_le
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.targetsSection_of_targetsSectionIndex
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.sourceArc_length_le_of_shortSection
