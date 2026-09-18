import GroupApproximation.Manuscript.NonMF.Full.GL06h3.OneCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixDescentCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52LeastArea
import GroupApproximation.GGT.VanKampen.Estimating.ShortSection
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h3: a short boundary around two or more cells, by the nearest cell

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

Let `Δ` be a least-area diagram with `n ≥ 2` relator cells and a short boundary `u`.  Take a
cell `Π` nearest to the boundary, joined to it by a geodesic path `p` of minimal length, and cut
`Δ` along `p` and around `Π`.  The remaining subdiagram `Ξ` has `n − 1` cells and boundary
`u p̂ R p̂⁻¹`, with `R` the boundary of `Π`.  Clause (b) of Lemma 9.7 below `n` at `Ξ` gives a
cell `Π'` of an O-equivalent copy with degree sum larger than `1 − 13μ` to these four sections.
A region to `u` has target arc at most `ε + ε`; a region to `p̂` or `p̂⁻¹` also, since `p` is
minimal; both have degree below `μ/2`.  A region to `R` becomes, after gluing `Π` back, a region
between two distinct cells of an O-equivalent copy of `Δ`, of degree below `μ` by O52.  The sum
is at most `5μ/2 < 1 − 13μ` for `μ ≤ 1/16`.

* `sourceArc_length_le_of_targetArc_le`: Osin's side-arc estimate at a target arc of length `L`.
* `contiguityDegree_lt_half_mu_of_targetArc_le`: degree below `μ/2` at a target arc `≤ ε + ε`.
* `NearestCellCut`: the cut along a minimal path to a nearest cell, as data.
* `NearestCellCut.false_of_below`: the count, from clause (b) below the relator count.
* `shortBoundaryRefutedBelowInput_of_parts`: the refutation at fixed parameters from the pointwise
  conclusion of GL06h2 and the nearest-cell cut.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h3

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## The side-arc estimate at a bounded target arc -/

/-- **Osin's side-arc estimate at a target arc of length `L`** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121).  A region to an admissible section of the boundary
whose target arc has length at most `L` has source arc at most `λ⁻¹(2ε + L + c)`. -/
theorem contiguity_sourceArc_length_le_of_targetArc_le {D : RelGenSet G Lambda}
    {W : Set (List (RelLetter G Lambda))} {eps rho : ℕ} {mu lambda c : ℝ}
    {Xi : DiscDiagram.{u, w, v} W} {faces : Finset Xi.toCombMap.Face}
    (Gamma : Contiguity D eps Xi faces) (q : List Xi.toCombMap.Dart)
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (htarget : Gamma.TargetsSection q)
    (hadmissible : HullSC.RelWord.IsAdmissible D (dartWord Xi q))
    {L : ℕ} (hL : Gamma.targetArc.length ≤ L) :
    (Gamma.sourceArc.length : ℝ) ≤ lambda⁻¹ * (2 * (eps : ℝ) + (L : ℝ) + c) := by
  have hnorm := Gamma.sourceArc_norm_le
  have hboundary : targetBoundaryDarts Xi Gamma.target Gamma.targetArc =
      Gamma.targetArc.darts := by
    exact (show ∀ (target : Option (Fin Xi.rCellCount))
        (arc : CyclicArc (targetDarts Xi target)), target = none →
          targetBoundaryDarts Xi target arc = arc.darts from by
      intro target arc h
      cases target with
      | none => rfl
      | some i => cases h) _ _ htarget.1
  rw [hboundary] at hnorm
  have htnorm := OsinComponents.wordNorm_listVal_le D
    (dartWord Xi Gamma.targetArc.darts) (by
      intro letter hletter
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hletter
      exact hadmissible _ (List.mem_map.mpr ⟨d, htarget.2 d hd, rfl⟩))
  have hlen : (dartWord Xi Gamma.targetArc.darts).length = Gamma.targetArc.length := by
    simp only [dartWord, List.length_map, CyclicArc.darts_length]
  have hupper : (wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord Xi Gamma.sourceArc.darts)) : ℝ) ≤
      2 * (eps : ℝ) + (L : ℝ) := by
    exact_mod_cast (show wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord Xi Gamma.sourceArc.darts)) ≤ 2 * eps + L by omega)
  have hlower := Gamma.sourceArc_quasi_lower hcondition
  rw [inv_mul_eq_div, le_div_iff₀ hlambda]
  nlinarith

/-- **Osin's side-arc estimate for a region to section `j`, at a target arc of length `L`**
(Osin, proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem sourceArc_length_le_of_targetArc_le {D : RelGenSet G Lambda}
    {W : Set (List (RelLetter G Lambda))} {eps rho : ℕ} {mu lambda c : ℝ}
    {word : List (RelLetter G Lambda)} {Xi : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c word} (hword : Xi.boundaryWord = word)
    {j : Fin cuts.count} (a : RegionCandidate D eps Xi)
    (h : RegionCandidate.TargetsSectionIndex cuts j a)
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    {L : ℕ} (hL : a.2.targetArc.length ≤ L) :
    (a.2.sourceArc.length : ℝ) ≤ lambda⁻¹ * (2 * (eps : ℝ) + (L : ℝ) + c) :=
  contiguity_sourceArc_length_le_of_targetArc_le (a.toContiguityOfTargetNone h.1)
    ((cuts.toBoundarySections Xi hword).part j) hcondition hlambda
    (RegionCandidate.targetsSection_of_targetsSectionIndex hword a h)
    ((cuts.toBoundarySections Xi hword).quasiGeodesic j).1 hL

/-- **Degree below `μ/2` at a target arc of length at most `ε + ε`** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121), once `λ⁻¹(4ε + c) < (μ/2)ρ`. -/
theorem contiguityDegree_lt_half_mu_of_targetArc_le {D : RelGenSet G Lambda}
    {W : Set (List (RelLetter G Lambda))} {eps rho : ℕ} {mu lambda c : ℝ}
    {word : List (RelLetter G Lambda)} {Xi : DiscDiagram.{u, w, v} W}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (4 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {cuts : SectionCuts D lambda c word} (hword : Xi.boundaryWord = word)
    {j : Fin cuts.count} (a : RegionCandidate D eps Xi)
    (h : RegionCandidate.TargetsSectionIndex cuts j a)
    (hL : a.2.targetArc.length ≤ eps + eps) :
    a.contiguityDegree < mu / 2 := by
  have hbound := sourceArc_length_le_of_targetArc_le hword a h hcondition hlambda hL
  have hconst : lambda⁻¹ * (2 * (eps : ℝ) + ((eps + eps : ℕ) : ℝ) + c) =
      lambda⁻¹ * (4 * (eps : ℝ) + c) := by
    push_cast
    ring
  have hlong : rho ≤ (cell Xi a.2.source).word.length :=
    hcondition.long (cell Xi a.2.source).word (cell Xi a.2.source).word_mem
  have hlongR : (rho : ℝ) ≤ ((cell Xi a.2.source).word.length : ℝ) := by
    exact_mod_cast hlong
  have hpos : (0 : ℝ) < ((cell Xi a.2.source).word.length : ℝ) :=
    cellWord_length_pos hcondition.toIsSmallCancellation hrho a.2.source
  have hhalf : (0 : ℝ) ≤ mu / 2 := by linarith
  have hmul : mu / 2 * (rho : ℝ) ≤ mu / 2 * ((cell Xi a.2.source).word.length : ℝ) :=
    mul_le_mul_of_nonneg_left hlongR hhalf
  unfold RegionCandidate.contiguityDegree
  rw [div_lt_iff₀ hpos]
  linarith

/-! ## The cut along a minimal path to a nearest cell -/

/-- **The cut along a minimal path to a nearest cell** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  A least-area subdiagram `Ξ` with at least one and fewer relator
cells than `Δ`, whose boundary is four sections `u p̂ R p̂⁻¹`:
* the section `u` has length at most `ε + ε`;
* a region of an O-equivalent copy of `Ξ` to `p̂` or `p̂⁻¹` has target arc at most `ε + ε`,
  since `p` is a shortest path from the boundary to a cell;
* a region of an O-equivalent copy of `Ξ` to `R` becomes, after gluing the nearest cell back, a
  region of an O-equivalent copy of `Δ` between two distinct cells, of the same degree. -/
structure NearestCellCut {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) where
  enclosed : DiscDiagram.{u, w, v} W
  leastArea : enclosed.LeastArea
  rCellCount_pos : 0 < enclosed.rCellCount
  rCellCount_lt : enclosed.rCellCount < Delta.rCellCount
  sections : SectionCuts D lambda c enclosed.boundaryWord
  count_eq : sections.count = 4
  side_short : ∀ j : Fin sections.count, (j : ℕ) = 0 →
    sections.cut j.succ - sections.cut j.castSucc ≤ eps + eps
  near : ∀ j : Fin sections.count, ((j : ℕ) = 1 ∨ (j : ℕ) = 3) →
    ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram enclosed Xi →
      ∀ a : RegionCandidate D eps Xi,
        RegionCandidate.TargetsSectionIndex sections j a →
          a.2.targetArc.length ≤ eps + eps
  transport : ∀ j : Fin sections.count, (j : ℕ) = 2 →
    ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram enclosed Xi →
      ∀ a : RegionCandidate D eps Xi,
        RegionCandidate.TargetsSectionIndex sections j a →
          ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
            (t : Fin Y.rCellCount),
            Nonempty (OEquivalentDiscDiagram Delta Y) ∧
              b.2.target = some t ∧ b.2.source ≠ t ∧
              b.contiguityDegree = a.contiguityDegree

/-! ## The count -/

/-- **Osin's contradiction at the nearest cell** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  Clause (b) below the relator count of `Δ`, applied to the cut,
gives a degree sum above `1 − 13μ`; the three short sections contribute below `μ/2` each and the
cell section below `μ` by O52, at most `5μ/2`, impossible for `μ ≤ 1/16`. -/
theorem NearestCellCut.false_of_below {D : RelGenSet G Lambda}
    {W : Set (List (RelLetter G Lambda))} {lambda c mu : ℝ} {eps rho : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    (cut : NearestCellCut D lambda c eps Delta)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (4 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hlea : Delta.LeastArea)
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount) :
    False := by
  obtain ⟨T, _source, present, region, _hsource, htargets, _hdisjoint, hsum⟩ :=
    hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt
  have hboundary : T.diagram.boundaryWord = cut.enclosed.boundaryWord :=
    T.equiv.boundaryWord_eq
  have hlarge3 : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) := by
    have hmono : lambda⁻¹ * (3 * (eps : ℝ) + c) ≤ lambda⁻¹ * (4 * (eps : ℝ) + c) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hlambda.le)
      have heps : (0 : ℝ) ≤ eps := Nat.cast_nonneg _
      linarith
    linarith
  have hbound : ∀ j ∈ present, (region j).contiguityDegree ≤
      (if (j : ℕ) = 2 then mu else mu / 2) := by
    intro j hj
    have hj4 : (j : ℕ) < 4 := by
      have hlt := j.isLt
      have hc := cut.count_eq
      omega
    by_cases hcell : (j : ℕ) = 2
    · rw [if_pos hcell]
      obtain ⟨Y, b, t, ⟨EY⟩, htarget, hne, hdeg⟩ :=
        cut.transport j hcell T.diagram T.equiv (region j) (htargets j hj)
      rw [← hdeg]
      exact le_of_lt (RegionCandidate.contiguityDegree_lt_mu_of_o52 Embedded.o52LeastArea
        hcondition hlambda hmu hrho hlarge3 (EY.leastArea hlea) b htarget hne)
    · rw [if_neg hcell]
      have hL : (region j).2.targetArc.length ≤ eps + eps := by
        by_cases hzero : (j : ℕ) = 0
        · have hs := cut.side_short j hzero
          have h1 := (htargets j hj).2.1
          have h2 := (htargets j hj).2.2
          omega
        · have hnear : (j : ℕ) = 1 ∨ (j : ℕ) = 3 := by omega
          exact cut.near j hnear T.diagram T.equiv (region j) (htargets j hj)
      exact le_of_lt (contiguityDegree_lt_half_mu_of_targetArc_le hcondition hlambda hmu hrho
        hlarge hboundary (region j) (htargets j hj) hL)
  have hle := Finset.sum_le_sum hbound
  have htotal : (∑ j ∈ present, (if (j : ℕ) = 2 then mu else mu / 2)) ≤
      ∑ j : Fin cut.sections.count, (if (j : ℕ) = 2 then mu else mu / 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ present)
    intro j _ _
    split_ifs <;> linarith
  have hfour : (∑ j : Fin cut.sections.count, (if (j : ℕ) = 2 then mu else mu / 2)) =
      5 * mu / 2 := by
    have hc := cut.count_eq
    revert hc
    generalize cut.sections.count = n
    intro hn
    subst hn
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
    norm_num <;> ring
  linarith

/-! ## The refutation at fixed parameters -/

/-- **A short boundary is refuted below the inductive bound, from its parts** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  One cell: the boundary word is a short
letter word conjugate to a nontrivial relator value (`false_of_oneCell`).  Two or more cells: a
least-area diagram of the same relator count carries a nearest-cell cut
(`NearestCellCut.false_of_below`). -/
theorem shortBoundaryRefutedBelowInput_of_parts {D : RelGenSet G Lambda}
    {W : Set (List (RelLetter G Lambda))} {lambda c mu : ℝ} {eps rho : ℕ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (4 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hconj : ∀ word ∈ W, RelLetter.listVal word ≠ 1 →
      ∀ (g : G) (u : List (RelLetter G Lambda)),
        (∀ x ∈ u, (symmetricLabelAlphabet D).IsLetter x) →
        u.length ≤ eps + eps →
          RelLetter.listVal u ≠ g * RelLetter.listVal word * g⁻¹)
    (hcut : ∀ Xi : DiscDiagram.{u, w, v} W, Xi.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (Xi.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Xi.rCellCount →
      Xi.boundaryWord.length ≤ eps + eps →
        ∃ Delta : DiscDiagram.{u, w, v} W, Delta.LeastArea ∧
          Delta.rCellCount = Xi.rCellCount ∧
          Nonempty (NearestCellCut D lambda c eps Delta)) :
    ShortBoundaryRefutedBelowInput.{u, w, v} D lambda c mu eps W := by
  intro Xi hlea hbelow hletters hW hpos hshort
  by_cases hone : Xi.rCellCount = 1
  · exact false_of_oneCell hcondition.inv_mem hconj Xi hlea hletters hone hshort
  · have htwo : 2 ≤ Xi.rCellCount := by omega
    obtain ⟨Delta, hleaD, hcount, ⟨cut⟩⟩ := hcut Xi hlea hletters hW htwo hshort
    rw [← hcount] at hbelow
    exact cut.false_of_below hcondition hlambda hmu hmuUpper hrho hlarge hleaD hbelow

end GroupApproximation.Full.GL06h3

#audit_axioms GroupApproximation.Full.GL06h3.contiguity_sourceArc_length_le_of_targetArc_le
#audit_axioms GroupApproximation.Full.GL06h3.sourceArc_length_le_of_targetArc_le
#audit_axioms GroupApproximation.Full.GL06h3.contiguityDegree_lt_half_mu_of_targetArc_le
#audit_axioms GroupApproximation.Full.GL06h3.NearestCellCut.false_of_below
#audit_axioms GroupApproximation.Full.GL06h3.shortBoundaryRefutedBelowInput_of_parts
