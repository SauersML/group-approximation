import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixAssemblyPocket
import Mathlib.Algebra.BigOperators.Field
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.7(b): the descent from named merge and step producers

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b).  `OsinAppendixAssemblyPocket`
proves the pocket estimate and the induction on `m(Π)` over the class of cells above
`1 − 13μ` (the approved threshold correction is recorded there).  This module names
the two geometric producers of that induction and assembles them:

* `OsinDescentMergeInput` — Osin's base case, `m(Π) = 0`;
* `OsinDescentStepInput` — Osin's step, `m(Π) > 0`: the pocket `Γ_1`, Corollary 9.6
  at the pocket (inequality (40) at `1 − 11μ`), at most one region to each of
  `s_1, t_1, s_2`, and the glue-back of the regions to `t_2` into a cell of smaller
  measure;
* `exists_exteriorUniqueAt_of_merge_step` — from a cell of the class, a realized
  family with a cell of the class having at most one exterior region per section;
* `exists_sectionSelection_of_exteriorUniqueAt` — such a cell gives one region per
  section, pairwise distinct, of total degree above `1 − 13μ`.

## Why the step carries Corollary 9.6 at the pocket (approved 2026-09-11, "F2")

Osin's (40) at `1 − 11μ` is obtained "by Corollary 9.6 and the inductive
assumption" at the pocket, i.e. from clause (a) `(∗)` and Lemma 9.4 at a smaller
diagram.  The inductive hypothesis `OsinLemma97Below` that `DescentInput` receives
carries only clause (b), which at the pocket gives one region per section of total
degree above `1 − 13μ`, hence only `1 − 15μ` towards `t_2`: the new cell would fall
out of the class and the descent would not close.  So the `11μ` cell of the pocket
is part of `OsinDescentStepInput`, and `DescentInput` stays unchanged.  The
alternative ("F1") was to let `OsinLemma97Below` carry clauses (a) and (b), which
the induction of `osinLemma97_atParameters_of_inputs` proves together, and to give
`DescentInput` the Euler count and Lemma 9.4 as further premises.

## The measure

`m(Π) = m_1 + ⋯ + m_r`, the number of `R`-cells of the pockets of `Π`, is geometric
data a producer supplies.  Both producers are stated over one `measure`, which is
all the induction needs.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## The two producers -/

/-- **Osin's base case of the descent.**  "If `m_1 = ⋯ = m_r = 0`, then each of the
sets `{Γ_{i,1}}, …, {Γ_{i,r}}` consists of at most one diagram.  Indeed otherwise one
could include at least 2 of them into a single `ε`-contiguity subdiagram, which
contradicts the definition of `M`."  With membership in `M` dropped from clause (b),
the inclusion is a construction: a cell of the class of measure `0` has, in some
realized section family, a cell of the class with at most one exterior region per
section (the exterior regions to one section and the `R`-cell-free pockets between
them merge). -/
def OsinDescentMergeInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda)))
    (measure : ∀ (Delta : DiscDiagram.{u, w, v} W)
      (cuts : SectionCuts D lambda c Delta.boundaryWord)
      (T : RealizedSectionFamily D lambda c eps Delta cuts), Fin T.diagram.rCellCount → ℕ) :
    Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ (T : RealizedSectionFamily D lambda c eps Delta cuts) (i : Fin T.diagram.rCellCount),
        T.ExteriorLarge mu i → measure Delta cuts T i = 0 →
          ∃ (T' : RealizedSectionFamily D lambda c eps Delta cuts)
            (i' : Fin T'.diagram.rCellCount),
            T'.ExteriorLarge mu i' ∧ T'.ExteriorUniqueAt i'

/-- **Osin's step of the descent.**  "Thus we may assume that `m_1 > 0`.  Then by
Corollary 9.6 and the inductive assumption, the subdiagram `Γ_1` contains an `R`-cell
`Π′` and `ε`-contiguity subdiagrams `Γ′_{i,1}, …, Γ′_{i,4}` of `Π′` to
`s_1, t_1, s_2, t_2`, respectively, such that
`Σ (Π′, Γ′_{i,1}, s_1) + ⋯ + Σ (Π′, Γ′_{i,4}, t_2) > 1 − 11μ` (40).  Note that
`k_2 ≤ 1` … Thus `k_1 ≤ 1` … Similarly `k_3 ≤ 1` … However `m(Π′) < m(Π)` since the
cell `Π′` counts in `m(Π)` but not in `m(Π′)`."

A cell of the class of positive measure has a pocket (`OsinExteriorDoubleCut`), a
realized section family on the pocket with a cell `k` above `1 − 11μ` (Corollary 9.6
at the pocket), at most one exterior region of `k` to each of `s_1, t_1, s_2`, and a
glue-back: a realized section family on `Δ` whose cell `i′` has the perimeter of `k`,
exterior regions at least as long as those of `k` to `t_2`, and smaller measure. -/
def OsinDescentStepInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda)))
    (measure : ∀ (Delta : DiscDiagram.{u, w, v} W)
      (cuts : SectionCuts D lambda c Delta.boundaryWord)
      (T : RealizedSectionFamily D lambda c eps Delta cuts), Fin T.diagram.rCellCount → ℕ) :
    Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ (T : RealizedSectionFamily D lambda c eps Delta cuts) (i : Fin T.diagram.rCellCount),
        T.ExteriorLarge mu i → 0 < measure Delta cuts T i →
          ∃ (cut : OsinExteriorDoubleCut D lambda c eps Delta)
            (P : RealizedSectionFamily D lambda c eps cut.enclosed cut.sections)
            (k : Fin P.diagram.rCellCount),
            (1 - 11 * mu) * ((cell P.diagram k).word.length : ℝ) <
                ∑ a ∈ RegionCandidate.exteriorAt P.family k, (a.2.sourceArc.length : ℝ) ∧
              (∀ j : Fin cut.sections.count, (j : ℕ) ≠ 3 →
                ∀ a ∈ RegionCandidate.exteriorAt P.family k,
                  ∀ b ∈ RegionCandidate.exteriorAt P.family k,
                    RegionCandidate.TargetsSectionIndex cut.sections j a →
                      RegionCandidate.TargetsSectionIndex cut.sections j b → a = b) ∧
              ∀ j3 : Fin cut.sections.count, (j3 : ℕ) = 3 →
                ∃ (T' : RealizedSectionFamily D lambda c eps Delta cuts)
                  (i' : Fin T'.diagram.rCellCount),
                  P.exteriorSectionLength k j3 ≤
                      ∑ a ∈ RegionCandidate.exteriorAt T'.family i',
                        (a.2.sourceArc.length : ℝ) ∧
                    ((cell T'.diagram i').word.length : ℝ) =
                      ((cell P.diagram k).word.length : ℝ) ∧
                    measure Delta cuts T' i' < measure Delta cuts T i

/-! ## The descent -/

/-- **A cell above `1 − 11μ` lies in the class at `1 − 13μ`.** -/
theorem RealizedSectionFamily.exteriorLarge_of_gt_eleven
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c mu : ℝ}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (T : RealizedSectionFamily D lambda c eps Delta cuts) (i : Fin T.diagram.rCellCount)
    (hmu : 0 ≤ mu)
    (h11 : (1 - 11 * mu) * ((cell T.diagram i).word.length : ℝ) <
      ∑ a ∈ RegionCandidate.exteriorAt T.family i, (a.2.sourceArc.length : ℝ)) :
    T.ExteriorLarge mu i := by
  unfold RealizedSectionFamily.ExteriorLarge
  have hnn : 0 ≤ mu * ((cell T.diagram i).word.length : ℝ) :=
    mul_nonneg hmu (Nat.cast_nonneg _)
  linarith

/-- **Osin's descent, assembled.**  From a cell of the class, the merge and step
producers give a realized family with a cell of the class having at most one
exterior region per section.  The step's `t_2` bound is the pocket estimate
`OsinExteriorDoubleCut.lastSection_total_gt`. -/
theorem exists_exteriorUniqueAt_of_merge_step
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ}
    (measure : ∀ (Delta : DiscDiagram.{u, w, v} W)
      (cuts : SectionCuts D lambda c Delta.boundaryWord)
      (T : RealizedSectionFamily D lambda c eps Delta cuts), Fin T.diagram.rCellCount → ℕ)
    (hmerge : OsinDescentMergeInput.{u, w, v} D lambda c mu eps W measure)
    (hstep : OsinDescentStepInput.{u, w, v} D lambda c mu eps W measure)
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (hlea : Delta.LeastArea)
    (T : RealizedSectionFamily D lambda c eps Delta cuts) (i : Fin T.diagram.rCellCount)
    (hT : T.ExteriorLarge mu i) :
    ∃ (T' : RealizedSectionFamily D lambda c eps Delta cuts)
      (i' : Fin T'.diagram.rCellCount),
      T'.ExteriorLarge mu i' ∧ T'.ExteriorUniqueAt i' := by
  refine exists_of_exteriorDescent (fun _ => True) (measure Delta cuts) ?_ ?_ T trivial i hT
  · intro T₀ _ i₀ hT₀ h0
    exact hmerge Delta cuts hlea T₀ i₀ hT₀ h0
  · intro T₀ _ i₀ hT₀ hpos
    obtain ⟨cut, P, k, h40, huniq, hglue⟩ := hstep Delta cuts hlea T₀ i₀ hT₀ hpos
    have hcount : 3 < cut.sections.count := by
      have hc := cut.count_eq
      omega
    have hlast := cut.lastSection_total_gt hO52 hcondition hlambda hmu hrho hlarge hlea P k
      h40 huniq ⟨3, hcount⟩ rfl
    obtain ⟨T', i', hle, hperim, hlt⟩ := hglue ⟨3, hcount⟩ rfl
    refine ⟨T', i', trivial, ?_, hlt⟩
    unfold RealizedSectionFamily.ExteriorLarge
    rw [hperim]
    linarith

/-! ## One region per section -/

/-- Every exterior region of a cell targets some section, so the exterior total at a
cell is at most the sum over the sections. -/
theorem RealizedSectionFamily.sum_exteriorAt_le_sum_sections
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (T : RealizedSectionFamily D lambda c eps Delta cuts) (i : Fin T.diagram.rCellCount) :
    (∑ a ∈ RegionCandidate.exteriorAt T.family i, (a.2.sourceArc.length : ℝ)) ≤
      ∑ j : Fin cuts.count, T.exteriorSectionLength i j := by
  unfold RealizedSectionFamily.exteriorSectionLength
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a ha => ?_
  obtain ⟨j0, hj0⟩ := T.respects a (RegionCandidate.mem_of_mem_exteriorAt ha)
    (RegionCandidate.target_eq_none_of_mem_exteriorAt ha)
  calc (a.2.sourceArc.length : ℝ)
      = (if RegionCandidate.TargetsSectionIndex cuts j0 a then
          (a.2.sourceArc.length : ℝ) else 0) := by rw [if_pos hj0]
    _ ≤ ∑ j : Fin cuts.count,
          (if RegionCandidate.TargetsSectionIndex cuts j a then
            (a.2.sourceArc.length : ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun j => if RegionCandidate.TargetsSectionIndex cuts j a then
            (a.2.sourceArc.length : ℝ) else 0)
          (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ j0)

/-- A region with a nonempty target arc targets at most one section. -/
theorem SectionCuts.eq_of_targetsSectionIndex
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {Xi : DiscDiagram.{u, w, v} W} {word : List (RelLetter G Lambda)}
    (cuts : SectionCuts D lambda c word) {a : RegionCandidate D eps Xi}
    (hlen : 0 < a.2.targetArc.length) {j k : Fin cuts.count}
    (hj : RegionCandidate.TargetsSectionIndex cuts j a)
    (hk : RegionCandidate.TargetsSectionIndex cuts k a) : j = k := by
  obtain ⟨-, hj1, hj2⟩ := hj
  obtain ⟨-, hk1, hk2⟩ := hk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hlt' : (j : ℕ) < (k : ℕ) := hlt
    have hmono : cuts.cut j.succ ≤ cuts.cut k.castSucc :=
      cuts.cut_mono (a := j.succ) (b := k.castSucc) (by show (j : ℕ) + 1 ≤ (k : ℕ); omega)
    omega
  · have hlt' : (k : ℕ) < (j : ℕ) := hlt
    have hmono : cuts.cut k.succ ≤ cuts.cut j.castSucc :=
      cuts.cut_mono (a := k.succ) (b := j.castSucc) (by show (k : ℕ) + 1 ≤ (j : ℕ); omega)
    omega

/-- **One region per section.**  A cell of the class with at most one exterior region
per section, in a family whose regions have nonempty target arcs, gives a source cell,
a set of present sections, and one region to each present section: members of the
family, from that cell, targeting their sections, pairwise distinct, of total degree
above `1 − 13μ`.  This is the shape of clause (b); with pairwise compatibility of the
family it gives Osin's disjointness. -/
theorem exists_sectionSelection_of_exteriorUniqueAt
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c mu : ℝ}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (T : RealizedSectionFamily D lambda c eps Delta cuts) (i : Fin T.diagram.rCellCount)
    (hlarge : T.ExteriorLarge mu i) (huniq : T.ExteriorUniqueAt i)
    (hnondeg : ∀ a ∈ T.family, 0 < a.2.targetArc.length)
    (hmuUpper : mu ≤ 1 / 16) (hpos : 0 < ((cell T.diagram i).word.length : ℝ)) :
    ∃ (source : Fin T.diagram.rCellCount) (present : Finset (Fin cuts.count))
      (region : Fin cuts.count → RegionCandidate D eps T.diagram),
      (∀ j ∈ present, region j ∈ T.family) ∧
        (∀ j ∈ present, (region j).2.source = source) ∧
        (∀ j ∈ present, RegionCandidate.TargetsSectionIndex cuts j (region j)) ∧
        (∀ j ∈ present, ∀ k ∈ present, j ≠ k → region j ≠ region k) ∧
        1 - 13 * mu < ∑ j ∈ present, (region j).contiguityDegree := by
  -- The exterior total is positive, so some exterior region exists.
  have hsum_pos : 0 < ∑ a ∈ RegionCandidate.exteriorAt T.family i, (a.2.sourceArc.length : ℝ) := by
    have hcoef : 0 < 1 - 13 * mu := by linarith
    have hprod := mul_pos hcoef hpos
    unfold RealizedSectionFamily.ExteriorLarge at hlarge
    linarith
  obtain ⟨a0, -⟩ : (RegionCandidate.exteriorAt T.family i).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hsum_pos
    exact lt_irrefl 0 hsum_pos
  -- One chosen region per section that has one.
  let p : Fin cuts.count → Prop := fun j =>
    ∃ a ∈ RegionCandidate.exteriorAt T.family i, RegionCandidate.TargetsSectionIndex cuts j a
  let region : Fin cuts.count → RegionCandidate D eps T.diagram := fun j =>
    if h : p j then Classical.choose h else a0
  have hspec : ∀ j, p j → region j ∈ RegionCandidate.exteriorAt T.family i ∧
      RegionCandidate.TargetsSectionIndex cuts j (region j) := by
    intro j hj
    have hr : region j = Classical.choose hj := dif_pos hj
    rw [hr]
    exact Classical.choose_spec hj
  refine ⟨i, Finset.univ.filter p, region, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact RegionCandidate.mem_of_mem_exteriorAt (hspec j (Finset.mem_filter.mp hj).2).1
  · intro j hj
    exact RegionCandidate.source_eq_of_mem_exteriorAt (hspec j (Finset.mem_filter.mp hj).2).1
  · intro j hj
    exact (hspec j (Finset.mem_filter.mp hj).2).2
  · intro j hj k hk hjk heq
    have hsj := hspec j (Finset.mem_filter.mp hj).2
    have hsk := hspec k (Finset.mem_filter.mp hk).2
    rw [heq] at hsj
    exact hjk (cuts.eq_of_targetsSectionIndex
      (hnondeg _ (RegionCandidate.mem_of_mem_exteriorAt hsk.1)) hsj.2 hsk.2)
  · -- Each section contributes at most its chosen region.
    have hsec : ∀ j : Fin cuts.count, T.exteriorSectionLength i j ≤
        (if p j then ((region j).2.sourceArc.length : ℝ) else 0) := by
      intro j
      unfold RealizedSectionFamily.exteriorSectionLength
      by_cases hj : p j
      · rw [if_pos hj]
        refine osinPocket_sum_le_of_subsingleton (Nat.cast_nonneg _) ?_ ?_
        · intro a ha b hb
          have ha' := Finset.mem_filter.mp ha
          have hb' := Finset.mem_filter.mp hb
          exact huniq j a ha'.1 b hb'.1 ha'.2 hb'.2
        · intro a ha
          have ha' := Finset.mem_filter.mp ha
          have heq : a = region j :=
            huniq j a ha'.1 (region j) (hspec j hj).1 ha'.2 (hspec j hj).2
          exact le_of_eq
            (congrArg (fun x : RegionCandidate D eps T.diagram => (x.2.sourceArc.length : ℝ)) heq)
      · rw [if_neg hj]
        have hempty : (RegionCandidate.exteriorAt T.family i).filter
            (fun a => RegionCandidate.TargetsSectionIndex cuts j a) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro a ha hta
          exact hj ⟨a, ha, hta⟩
        simp only [hempty, Finset.sum_empty, le_refl]
    have hle1 := T.sum_exteriorAt_le_sum_sections i
    have hle2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hsec j
    have hfilt : (∑ j ∈ Finset.univ.filter p, ((region j).2.sourceArc.length : ℝ)) =
        ∑ j : Fin cuts.count, (if p j then ((region j).2.sourceArc.length : ℝ) else 0) :=
      Finset.sum_filter _ _
    have hdeg : (∑ j ∈ Finset.univ.filter p, (region j).contiguityDegree) =
        (∑ j ∈ Finset.univ.filter p, ((region j).2.sourceArc.length : ℝ)) /
          ((cell T.diagram i).word.length : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hsrc : (region j).2.source = i :=
        RegionCandidate.source_eq_of_mem_exteriorAt (hspec j (Finset.mem_filter.mp hj).2).1
      have hcell : ((cell T.diagram (region j).2.source).word.length : ℝ) =
          ((cell T.diagram i).word.length : ℝ) := by
        rw [hsrc]
      unfold RegionCandidate.contiguityDegree
      rw [hcell]
    rw [hdeg, lt_div_iff₀ hpos]
    unfold RealizedSectionFamily.ExteriorLarge at hlarge
    linarith

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinDescentMergeInput
#audit_axioms GroupApproximation.GGT.VanKampen.OsinDescentStepInput
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.exteriorLarge_of_gt_eleven
#audit_axioms GroupApproximation.GGT.VanKampen.exists_exteriorUniqueAt_of_merge_step
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.sum_exteriorAt_le_sum_sections
#audit_axioms GroupApproximation.GGT.VanKampen.SectionCuts.eq_of_targetsSectionIndex
#audit_axioms GroupApproximation.GGT.VanKampen.exists_sectionSelection_of_exteriorUniqueAt
