import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionCounting
import GroupApproximation.Meta.AxiomGuard

/-!
# The descent of Osin's Lemma 9.7(b): the pocket estimate and the induction on `m(Π)`

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "By (a), we can choose an `R`-cell `Π` in `Δ` … and subdiagrams `Γ_{i,j}`
> satisfying the inequality in Corollary 9.6.  Let us consider the subdiagram `Γ_1`
> of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1, s_2` are side arcs of
> some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the section `q_1` of
> `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s.  Let `m_1` be the number
> of `R`-cells in `Γ_1`. … Suppose that the cell `Π` is chosen in such a way that
> the sum `m(Π) = m_1 + … + m_r` is minimal …  Then by Corollary 9.6 and the
> inductive assumption, the subdiagram `Γ_1` contains an `R`-cell `Π′` and
> `ε`-contiguity subdiagrams `Γ′_{i,1}, …, Γ′_{i,4}` of `Π′` to `s_1, t_1, s_2, t_2`
> … such that `Σ (Π′, Γ′_{i,1}, s_1) + ⋯ + Σ (Π′, Γ′_{i,4}, t_2) > 1 − 11μ` (40).
> Note that `k_2 ≤ 1` … `(Π′, Γ′_{1,2}, t_1) < μ` by Lemma 4.3. … Thus `k_1 ≤ 1`
> and if `k_1 = 1` we obtain `(Π′, Γ′_{i,1}, s_1) < μ/2` … Similarly `k_3 ≤ 1` …
> These inequalities together with (40) imply `Σ (Π′, Γ′_{i,4}, t_2) > 1 − 13μ`.
> However `m(Π′) < m(Π)` …  This contradicts the choice of `Π`."

## The threshold correction (approved 2026-09-11)

As printed, `Π` minimises `m(Π)` among the cells with total degree above `1 − 11μ`,
while the new cell `Π′` is only shown to have total degree above `1 − 13μ` towards
`t_2`; so `Π′` need not lie in the class, and "contradicts the choice of `Π`" does
not follow as written.  The class is taken here at `1 − 13μ`
(`RealizedSectionFamily.ExteriorLarge`).  It is nonempty because Corollary 9.6
gives a cell above `1 − 11μ`, and every step that uses `Π`'s bound holds at `13μ`,
since the pocket estimate below needs Corollary 9.6's `11μ` only at the pocket.
The final `1 − 13μ > 3μ` holds for `μ < 1/16`.

## What is proved here

* `OsinExteriorDoubleCut`: the pocket `Γ_1`, as a named geometric input, with its
  four sections `s_1 t_1 s_2 t_2`, the side arcs short and the regions to `t_1`
  transported to cell-to-cell regions of an O-equivalent copy of `Δ`;
* `OsinExteriorDoubleCut.lastSection_total_gt`: Osin's estimate — from (40) at a
  cell of a realized family on the pocket, and at most one region to each of
  `s_1, t_1, s_2`, the regions to `t_2` total above `1 − 13μ`.  Every numeric step
  is proved: the side-arc degree bound `< μ/2`, the O52 degree bound `< μ`, and
  the count;
* `exists_of_exteriorDescent`: the induction on `m(Π)` over the class at `1 − 13μ`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## The class at `1 − 13μ` -/

/-- **A cell of a realized section family above `1 − 13μ`**: its exterior regions
have total source length above `(1 − 13μ)` times its perimeter. -/
def RealizedSectionFamily.ExteriorLarge {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord} (mu : ℝ)
    (T : RealizedSectionFamily D lambda c eps Delta cuts) (i : Fin T.diagram.rCellCount) :
    Prop :=
  (1 - 13 * mu) * ((cell T.diagram i).word.length : ℝ) <
    ∑ a ∈ RegionCandidate.exteriorAt T.family i, (a.2.sourceArc.length : ℝ)

/-- **At most one exterior region of a cell per section.** -/
def RealizedSectionFamily.ExteriorUniqueAt {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (T : RealizedSectionFamily D lambda c eps Delta cuts) (i : Fin T.diagram.rCellCount) :
    Prop :=
  ∀ j : Fin cuts.count, ∀ a ∈ RegionCandidate.exteriorAt T.family i,
    ∀ b ∈ RegionCandidate.exteriorAt T.family i,
      RegionCandidate.TargetsSectionIndex cuts j a →
        RegionCandidate.TargetsSectionIndex cuts j b → a = b

/-- The total source length of the exterior regions of cell `i` to section `j`. -/
noncomputable def RealizedSectionFamily.exteriorSectionLength
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (T : RealizedSectionFamily D lambda c eps Delta cuts) (i : Fin T.diagram.rCellCount)
    (j : Fin cuts.count) : ℝ :=
  ∑ a ∈ (RegionCandidate.exteriorAt T.family i).filter
      (fun a => RegionCandidate.TargetsSectionIndex cuts j a),
    (a.2.sourceArc.length : ℝ)

/-! ## Membership facts for exterior regions -/

section Members

variable {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}

/-- An exterior region at a cell belongs to the family. -/
theorem RegionCandidate.mem_of_mem_exteriorAt
    {selected : Finset (RegionCandidate D eps Delta)} {i : Fin Delta.rCellCount}
    {a : RegionCandidate D eps Delta} (ha : a ∈ RegionCandidate.exteriorAt selected i) :
    a ∈ selected :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1

/-- An exterior region at a cell has that cell as its source. -/
theorem RegionCandidate.source_eq_of_mem_exteriorAt
    {selected : Finset (RegionCandidate D eps Delta)} {i : Fin Delta.rCellCount}
    {a : RegionCandidate D eps Delta} (ha : a ∈ RegionCandidate.exteriorAt selected i) :
    a.2.source = i :=
  (Finset.mem_filter.mp ha).2

/-- An exterior region targets the outer boundary. -/
theorem RegionCandidate.target_eq_none_of_mem_exteriorAt
    {selected : Finset (RegionCandidate D eps Delta)} {i : Fin Delta.rCellCount}
    {a : RegionCandidate D eps Delta} (ha : a ∈ RegionCandidate.exteriorAt selected i) :
    a.2.target = none :=
  RegionCandidate.target_eq_none_of_mem_ofKind_false (Finset.mem_filter.mp ha).1

/-- A degree bound at an exterior region of cell `i` is a length bound against the
perimeter of `i`. -/
theorem RegionCandidate.sourceArc_length_lt_of_contiguityDegree_lt
    {selected : Finset (RegionCandidate D eps Delta)} {i : Fin Delta.rCellCount}
    {a : RegionCandidate D eps Delta} (ha : a ∈ RegionCandidate.exteriorAt selected i)
    (hpos : 0 < ((cell Delta i).word.length : ℝ)) {B : ℝ} (hB : a.contiguityDegree < B) :
    (a.2.sourceArc.length : ℝ) < B * ((cell Delta i).word.length : ℝ) := by
  have hcell : ((cell Delta a.2.source).word.length : ℝ) = ((cell Delta i).word.length : ℝ) := by
    rw [RegionCandidate.source_eq_of_mem_exteriorAt ha]
  unfold RegionCandidate.contiguityDegree at hB
  rw [hcell, div_lt_iff₀ hpos] at hB
  exact hB

end Members

/-- A sum over a finset with at most one element is bounded by any nonnegative
bound on its terms. -/
theorem osinPocket_sum_le_of_subsingleton {α : Type*} {s : Finset α} {f : α → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (heq : ∀ a ∈ s, ∀ b ∈ s, a = b) (hle : ∀ a ∈ s, f a ≤ B) :
    ∑ a ∈ s, f a ≤ B := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simpa using hB
  · have hs : s = {a} := Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, fun x hx => heq x hx a ha⟩
    rw [hs, Finset.sum_singleton]
    exact hle a ha

/-! ## The pocket, as a named input -/

/-- **The pocket between exterior regions of one cell to one section** (Osin's
`Γ_1`), a named geometric input.  A least-area subdiagram with at least one and
fewer relator cells than `Δ`, whose boundary is four sections `s_1 t_1 s_2 t_2`:
the side arcs `s_1, s_2` of length at most `ε`, `t_1` a subpath of `∂Π` and `t_2` a
subpath of the section `q_j` of `∂Δ`.  A region to `t_1` in any O-equivalent copy
of the pocket becomes, after gluing, a region of an O-equivalent copy of `Δ` from a
cell to the cell `Π`, with the same contiguity degree. -/
structure OsinExteriorDoubleCut {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) where
  enclosed : DiscDiagram.{u, w, v} W
  leastArea : enclosed.LeastArea
  rCellCount_pos : 0 < enclosed.rCellCount
  rCellCount_lt : enclosed.rCellCount < Delta.rCellCount
  sections : SectionCuts D lambda c enclosed.boundaryWord
  count_eq : sections.count = 4
  side_short : ∀ j : Fin sections.count, ((j : ℕ) = 0 ∨ (j : ℕ) = 2) →
    sections.cut j.succ - sections.cut j.castSucc ≤ eps
  cellTransport : ∀ j : Fin sections.count, (j : ℕ) = 1 →
    ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram enclosed Xi →
      ∀ a : RegionCandidate D eps Xi,
        RegionCandidate.TargetsSectionIndex sections j a →
          ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
            (t : Fin Y.rCellCount),
            Nonempty (OEquivalentDiscDiagram Delta Y) ∧
              b.2.target = some t ∧ b.2.source ≠ t ∧
              b.contiguityDegree = a.contiguityDegree

/-- **Osin's pocket estimate.**  At a cell of a realized family on the pocket
whose exterior regions total above `1 − 11μ` (Corollary 9.6 at the pocket, (40)),
with at most one region to each of `s_1, t_1, s_2`, the regions to `t_2` total above
`1 − 13μ`: a region to `s_1` or `s_2` has degree below `μ/2` (the side-arc estimate)
and a region to `t_1` below `μ` (O52 after gluing). -/
theorem OsinExteriorDoubleCut.lastSection_total_gt
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (cut : OsinExteriorDoubleCut D lambda c eps Delta)
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hlea : Delta.LeastArea)
    (T : RealizedSectionFamily D lambda c eps cut.enclosed cut.sections)
    (i : Fin T.diagram.rCellCount)
    (h40 : (1 - 11 * mu) * ((cell T.diagram i).word.length : ℝ) <
      ∑ a ∈ RegionCandidate.exteriorAt T.family i, (a.2.sourceArc.length : ℝ))
    (hunique : ∀ j : Fin cut.sections.count, (j : ℕ) ≠ 3 →
      ∀ a ∈ RegionCandidate.exteriorAt T.family i,
        ∀ b ∈ RegionCandidate.exteriorAt T.family i,
          RegionCandidate.TargetsSectionIndex cut.sections j a →
            RegionCandidate.TargetsSectionIndex cut.sections j b → a = b)
    (j3 : Fin cut.sections.count) (hj3 : (j3 : ℕ) = 3) :
    (1 - 13 * mu) * ((cell T.diagram i).word.length : ℝ) < T.exteriorSectionLength i j3 := by
  have hpos : (0 : ℝ) < ((cell T.diagram i).word.length : ℝ) :=
    cellWord_length_pos hcondition.toIsSmallCancellation hrho i
  have hboundary : T.diagram.boundaryWord = cut.enclosed.boundaryWord :=
    T.equiv.boundaryWord_eq
  -- Every exterior region targets some section.
  have hsplit : (∑ a ∈ RegionCandidate.exteriorAt T.family i, (a.2.sourceArc.length : ℝ)) ≤
      ∑ j : Fin cut.sections.count, T.exteriorSectionLength i j := by
    unfold RealizedSectionFamily.exteriorSectionLength
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun a ha => ?_
    obtain ⟨j0, hj0⟩ := T.respects a (RegionCandidate.mem_of_mem_exteriorAt ha)
      (RegionCandidate.target_eq_none_of_mem_exteriorAt ha)
    calc (a.2.sourceArc.length : ℝ)
        = (if RegionCandidate.TargetsSectionIndex cut.sections j0 a then
            (a.2.sourceArc.length : ℝ) else 0) := by rw [if_pos hj0]
      _ ≤ ∑ j : Fin cut.sections.count,
            (if RegionCandidate.TargetsSectionIndex cut.sections j a then
              (a.2.sourceArc.length : ℝ) else 0) :=
          Finset.single_le_sum
            (f := fun j => if RegionCandidate.TargetsSectionIndex cut.sections j a then
              (a.2.sourceArc.length : ℝ) else 0)
            (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ j0)
  -- The bound for the three other sections.
  set perim : ℝ := ((cell T.diagram i).word.length : ℝ) with hperim
  have hbound : ∀ j ∈ Finset.univ.erase j3, T.exteriorSectionLength i j ≤
      (if (j : ℕ) = 3 then 0 else if (j : ℕ) = 1 then mu * perim else mu / 2 * perim) := by
    intro j hj
    have hne : j ≠ j3 := (Finset.mem_erase.mp hj).1
    have hj3' : (j : ℕ) ≠ 3 := fun h' => hne (Fin.ext (h'.trans hj3.symm))
    rw [if_neg hj3']
    unfold RealizedSectionFamily.exteriorSectionLength
    have hB : (0 : ℝ) ≤ (if (j : ℕ) = 1 then mu * perim else mu / 2 * perim) := by
      split_ifs
      exacts [(mul_pos hmu hpos).le, (mul_pos (half_pos hmu) hpos).le]
    refine osinPocket_sum_le_of_subsingleton hB ?_ ?_
    · intro a ha b hb
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      exact hunique j hj3' a ha'.1 b hb'.1 ha'.2 hb'.2
    · intro a ha
      have ha' := Finset.mem_filter.mp ha
      by_cases h1 : (j : ℕ) = 1
      · rw [if_pos h1]
        obtain ⟨Y, b, t, ⟨EY⟩, htarget, hne', hdeg⟩ :=
          cut.cellTransport j h1 T.diagram T.equiv a ha'.2
        have hdegb := RegionCandidate.contiguityDegree_lt_mu_of_o52 hO52 hcondition hrho
          (EY.leastArea hlea) b htarget hne'
        rw [hdeg] at hdegb
        exact le_of_lt (RegionCandidate.sourceArc_length_lt_of_contiguityDegree_lt ha'.1 hpos
          hdegb)
      · rw [if_neg h1]
        have h02 : (j : ℕ) = 0 ∨ (j : ℕ) = 2 := by
          have hlt := j.isLt
          have hc := cut.count_eq
          omega
        have hdeg := RegionCandidate.contiguityDegree_lt_half_mu_of_shortSection hcondition
          hlambda hmu hrho hlarge cut.sections hboundary (cut.side_short j h02) a ha'.2
        exact le_of_lt (RegionCandidate.sourceArc_length_lt_of_contiguityDegree_lt ha'.1 hpos
          hdeg)
  have herase := Finset.sum_le_sum hbound
  have hsubset : (∑ j ∈ Finset.univ.erase j3,
        (if (j : ℕ) = 3 then 0 else if (j : ℕ) = 1 then mu * perim else mu / 2 * perim)) ≤
      ∑ j : Fin cut.sections.count,
        (if (j : ℕ) = 3 then 0 else if (j : ℕ) = 1 then mu * perim else mu / 2 * perim) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset j3 Finset.univ)
    intro j _ _
    split_ifs
    exacts [le_rfl, (mul_pos hmu hpos).le, (mul_pos (half_pos hmu) hpos).le]
  have hfour : (∑ j : Fin cut.sections.count,
      (if (j : ℕ) = 3 then 0 else if (j : ℕ) = 1 then mu * perim else mu / 2 * perim)) =
        2 * mu * perim := by
    have hc := cut.count_eq
    revert hc
    generalize cut.sections.count = n
    intro hn
    subst hn
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
    norm_num
    all_goals ring
  have hadd := Finset.add_sum_erase Finset.univ (T.exteriorSectionLength i) (Finset.mem_univ j3)
  linarith

/-! ## The induction on `m(Π)` -/

/-- **Osin's descent, the induction on `m(Π)`**, over the class at `1 − 13μ` (see
the module header for the correction of the printed threshold).  `measure` is
`m(Π)`, the number of relator cells in the pockets of a cell; `P` is whatever
invariant the producers keep.  A class member of measure `0` gives the conclusion
(`hbase`: the regions to each section merge), and one of positive measure has a
class member of smaller measure in a pocket (`hstep`: the pocket estimate). -/
theorem exists_of_exteriorDescent {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c mu : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (P : RealizedSectionFamily D lambda c eps Delta cuts → Prop)
    (measure : (T : RealizedSectionFamily D lambda c eps Delta cuts) →
      Fin T.diagram.rCellCount → ℕ)
    {Q : Prop}
    (hbase : ∀ T, P T → ∀ i, T.ExteriorLarge mu i → measure T i = 0 → Q)
    (hstep : ∀ T, P T → ∀ i, T.ExteriorLarge mu i → 0 < measure T i →
      ∃ (T' : RealizedSectionFamily D lambda c eps Delta cuts)
        (i' : Fin T'.diagram.rCellCount),
        P T' ∧ T'.ExteriorLarge mu i' ∧ measure T' i' < measure T i)
    (T : RealizedSectionFamily D lambda c eps Delta cuts) (hT : P T)
    (i : Fin T.diagram.rCellCount) (hlarge : T.ExteriorLarge mu i) : Q := by
  have key : ∀ (n : ℕ) (T : RealizedSectionFamily D lambda c eps Delta cuts)
      (i : Fin T.diagram.rCellCount), measure T i = n → P T → T.ExteriorLarge mu i → Q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro T i hn hT hlarge
        by_cases hzero : measure T i = 0
        · exact hbase T hT i hlarge hzero
        · obtain ⟨T', i', hT', hlarge', hlt⟩ :=
            hstep T hT i hlarge (Nat.pos_of_ne_zero hzero)
          exact ih (measure T' i') (by omega) T' i' rfl hT' hlarge'
  exact key (measure T i) T i rfl hT hlarge

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.ExteriorLarge
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.ExteriorUniqueAt
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.exteriorSectionLength
#audit_axioms GroupApproximation.GGT.VanKampen.RegionCandidate.mem_of_mem_exteriorAt
#audit_axioms GroupApproximation.GGT.VanKampen.RegionCandidate.source_eq_of_mem_exteriorAt
#audit_axioms GroupApproximation.GGT.VanKampen.RegionCandidate.target_eq_none_of_mem_exteriorAt
#audit_axioms GroupApproximation.GGT.VanKampen.RegionCandidate.sourceArc_length_lt_of_contiguityDegree_lt
#audit_axioms GroupApproximation.GGT.VanKampen.osinPocket_sum_le_of_subsingleton
#audit_axioms GroupApproximation.GGT.VanKampen.OsinExteriorDoubleCut
#audit_axioms GroupApproximation.GGT.VanKampen.OsinExteriorDoubleCut.lastSection_total_gt
#audit_axioms GroupApproximation.GGT.VanKampen.exists_of_exteriorDescent
