import GroupApproximation.GGT.HullSCLemma51LetterWords
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.Meta.AxiomGuard

/-!
# Section cuts from quasi-geodesic parts

Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems*, arXiv:math/0411039v3, §9, proof of Lemma 9.7.  When two distinct
contiguity regions join the same two cells, the proof cuts out the subdiagram
`Ξ` with `∂Ξ = s_1 t_1 s_2 t_2`, where `s_1`, `s_2` are sides of the two regions
and `t_1`, `t_2` are arcs of the two cells, and it applies the induction
hypothesis to `Ξ` with these four sections.  This module proves the word-level
half of that step.

* An infix of a `(λ, c)`-quasi-geodesic word is `(λ, c)`-quasi-geodesic.  So
  under Osin's condition `C(ε, μ, λ, c, ρ)` every arc of a relator cell, read in
  either direction, is `(λ, c)`-quasi-geodesic, because the family is closed
  under cyclic permutation and formal inversion.
* A geodesic word `g` is `(λ, c)`-quasi-geodesic as soon as `0 ≤ c` and
  `(λ - 1) |g| ≤ c`.  Both inequalities follow from any quasi-geodesic word of
  length at least `|g|`, which covers the geodesic connector words along the
  sides `s_1`, `s_2`.
* `SectionCuts.ofParts` turns a decomposition of a boundary word into at most
  four quasi-geodesic parts into `SectionCuts` whose sections are the parts.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.HullSC
open GroupApproximation.WordMetric

universe u w

namespace CutSections

/-! ## Cut positions of a list of parts -/

/-- The position in `parts.flatten` at which part `k` begins. -/
def partsCut {α : Type*} (parts : List (List α)) (k : ℕ) : ℕ :=
  (parts.take k).flatten.length

theorem partsCut_zero {α : Type*} (parts : List (List α)) : partsCut parts 0 = 0 := by
  simp [partsCut]

theorem partsCut_length {α : Type*} (parts : List (List α)) :
    partsCut parts parts.length = parts.flatten.length := by
  unfold partsCut
  rw [List.take_of_length_le (Nat.le_refl _)]

theorem partsCut_mono {α : Type*} (parts : List (List α)) {a b : ℕ} (hab : a ≤ b) :
    partsCut parts a ≤ partsCut parts b := by
  unfold partsCut
  have htake : parts.take b = parts.take a ++ (parts.drop a).take (b - a) := by
    rw [← List.take_add]
    congr 1
    omega
  rw [htake, List.flatten_append, List.length_append]
  omega

theorem partsCut_succ {α : Type*} (parts : List (List α)) {j : ℕ} (hj : j < parts.length) :
    partsCut parts (j + 1) = partsCut parts j + parts[j].length := by
  unfold partsCut
  rw [List.take_add, List.drop_eq_getElem_cons hj]
  simp

/-- Part `j` sits in `parts.flatten` at position `partsCut parts j`. -/
theorem flatten_drop_partsCut_take {α : Type*} (parts : List (List α)) {j : ℕ}
    (hj : j < parts.length) :
    (parts.flatten.drop (partsCut parts j)).take parts[j].length = parts[j] := by
  have hparts : parts = parts.take j ++ parts[j] :: parts.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hsplit := congrArg List.flatten hparts
  simp only [List.flatten_append, List.flatten_cons] at hsplit
  unfold partsCut
  rw [hsplit, List.drop_left, List.take_left]

/-! ## Quasi-geodesic infixes and geodesic words -/

section QuasiGeodesic

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **Infixes.**  An infix of a `(λ, c)`-quasi-geodesic word is
`(λ, c)`-quasi-geodesic: its vertices are a left translate of a run of the
vertices of the whole word. -/
theorem isLambdaCQuasiGeodesicWord_infix {D : GGT.RelGenSet G Lambda} {lambda c : ℝ}
    {pre s post : List (GGT.RelLetter G Lambda)}
    (h : IsLambdaCQuasiGeodesicWord D lambda c (pre ++ s ++ post)) :
    IsLambdaCQuasiGeodesicWord D lambda c s := by
  refine ⟨?_, ?_⟩
  · intro a ha
    exact h.1 a (by simp [ha])
  · intro i j hij hj
    have hv : ∀ k, k ≤ s.length →
        GGT.OsinComponents.vertex 1 (pre ++ s ++ post) (pre.length + k)
          = GGT.RelLetter.listVal pre * GGT.OsinComponents.vertex 1 s k := by
      intro k hk
      rw [HullSC.vertex_eq_mul_listVal_take, HullSC.vertex_eq_mul_listVal_take, one_mul,
        one_mul, List.append_assoc, List.take_length_add_append,
        HullSC.RelWord.listVal_append, List.take_append_of_le_length hk]
    have key := h.2 (pre.length + i) (pre.length + j) (by omega)
      (by simp only [List.length_append]; omega)
    rw [hv i (by omega), hv j hj, wordDist_left_invariant,
      show pre.length + j - (pre.length + i) = j - i by omega] at key
    exact key

/-- A run `(word.drop a).take b` of a `(λ, c)`-quasi-geodesic word is
`(λ, c)`-quasi-geodesic. -/
theorem isLambdaCQuasiGeodesicWord_drop_take {D : GGT.RelGenSet G Lambda} {lambda c : ℝ}
    {word : List (GGT.RelLetter G Lambda)}
    (h : IsLambdaCQuasiGeodesicWord D lambda c word) (a b : ℕ) :
    IsLambdaCQuasiGeodesicWord D lambda c ((word.drop a).take b) := by
  have hsplit : word.take a ++ (word.drop a).take b ++ (word.drop a).drop b = word := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  rw [← hsplit] at h
  exact isLambdaCQuasiGeodesicWord_infix h

/-- The vertices of an admissible word are at most their index distance apart. -/
theorem wordDist_vertex_le (D : GGT.RelGenSet G Lambda)
    {word : List (GGT.RelLetter G Lambda)} (hadm : RelWord.IsAdmissible D word)
    {i j : ℕ} (hij : i ≤ j) :
    wordDist D.alphabet.carrier (GGT.OsinComponents.vertex 1 word i)
      (GGT.OsinComponents.vertex 1 word j) ≤ j - i := by
  have hl : ∀ x ∈ word.map GGT.RelLetter.val, x ∈ D.alphabet.carrier := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact HullSC.RelativeBoundaryContiguity.val_mem_alphabet_of_isLetter D (hadm a ha)
  have h := DiscreteStokes.wordDist_take_le hl 1 hij
  simp only [one_mul] at h
  rw [HullSC.vertex_one_eq_prod_take, HullSC.vertex_one_eq_prod_take]
  exact h

/-- The additive constant of a quasi-geodesic word is nonnegative (take
`i = j = 0`). -/
theorem c_nonneg_of_isLambdaCQuasiGeodesicWord {D : GGT.RelGenSet G Lambda}
    {lambda c : ℝ} {word : List (GGT.RelLetter G Lambda)}
    (h : IsLambdaCQuasiGeodesicWord D lambda c word) : 0 ≤ c := by
  have h0 := h.2 0 0 le_rfl (Nat.zero_le _)
  simp only [wordDist_self, Nat.sub_self, Nat.cast_zero, mul_zero, zero_sub] at h0
  linarith

/-- A `(λ, c)`-quasi-geodesic word of length at least `n` gives
`(λ - 1) n ≤ c`, because its vertices are at most their index distance apart. -/
theorem sub_one_mul_le_of_isLambdaCQuasiGeodesicWord {D : GGT.RelGenSet G Lambda}
    {lambda c : ℝ} {word : List (GGT.RelLetter G Lambda)}
    (h : IsLambdaCQuasiGeodesicWord D lambda c word) {n : ℕ} (hn : n ≤ word.length) :
    (lambda - 1) * (n : ℝ) ≤ c := by
  have h0 := h.2 0 n (Nat.zero_le n) hn
  have hd := wordDist_vertex_le D h.1 (Nat.zero_le n)
  rw [Nat.sub_zero] at h0 hd
  have hd' : ((wordDist D.alphabet.carrier (GGT.OsinComponents.vertex 1 word 0)
      (GGT.OsinComponents.vertex 1 word n) : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hd
  have hlin : (lambda - 1) * (n : ℝ) = lambda * (n : ℝ) - (n : ℝ) := by ring
  rw [hlin]
  linarith

/-- **Geodesic words.**  A geodesic admissible word `g` is
`(λ, c)`-quasi-geodesic when `0 ≤ c` and `(λ - 1) |g| ≤ c`. -/
theorem isLambdaCQuasiGeodesicWord_of_geodesic (D : GGT.RelGenSet G Lambda) {lambda c : ℝ}
    {word : List (GGT.RelLetter G Lambda)} (hadm : RelWord.IsAdmissible D word)
    (hgeo : word.length = wordNorm D.alphabet.carrier (GGT.RelLetter.listVal word))
    (hc : 0 ≤ c) (hslope : (lambda - 1) * (word.length : ℝ) ≤ c) :
    IsLambdaCQuasiGeodesicWord D lambda c word := by
  refine ⟨hadm, ?_⟩
  intro i j hij hj
  rw [HullSC.wordDist_vertex_of_geodesic D hadm hgeo hij hj]
  have hji : ((j - i : ℕ) : ℝ) ≤ (word.length : ℝ) := Nat.cast_le.mpr (by omega)
  have h0 : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) := Nat.cast_nonneg _
  by_cases hl : lambda ≤ 1
  · have hprod := mul_nonneg (sub_nonneg.mpr hl) h0
    nlinarith [hprod, hc]
  · have hprod := mul_le_mul_of_nonneg_left hji (sub_pos.mpr (not_le.mp hl)).le
    nlinarith [hprod, hslope]

/-- Under `C(ε, μ, λ, c, ρ)`, an infix of a relator is `(λ, c)`-quasi-geodesic. -/
theorem isLambdaCQuasiGeodesicWord_of_infix_mem {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcond : OsinCCondition D W eps mu lambda c rho)
    {pre s post : List (GGT.RelLetter G Lambda)} (hmem : pre ++ s ++ post ∈ W) :
    IsLambdaCQuasiGeodesicWord D lambda c s :=
  isLambdaCQuasiGeodesicWord_infix (hcond.quasiGeodesic _ hmem)

/-- Under `C(ε, μ, λ, c, ρ)`, a prefix of a cyclic permutation of a relator is
`(λ, c)`-quasi-geodesic.  This is the forward reading of an arc of a cell. -/
theorem isLambdaCQuasiGeodesicWord_rotate_take {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcond : OsinCCondition D W eps mu lambda c rho)
    {v : List (GGT.RelLetter G Lambda)} (hv : v ∈ W) (k n : ℕ) :
    IsLambdaCQuasiGeodesicWord D lambda c ((v.rotate k).take n) := by
  have h := isLambdaCQuasiGeodesicWord_drop_take
    (hcond.quasiGeodesic _ (hcond.rotate_mem v hv k)) 0 n
  rwa [List.drop_zero] at h

/-- Under `C(ε, μ, λ, c, ρ)`, the formal inverse of a prefix of a cyclic
permutation of a relator is `(λ, c)`-quasi-geodesic.  This is the backward
reading of an arc of a cell. -/
theorem isLambdaCQuasiGeodesicWord_revInv_rotate_take {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcond : OsinCCondition D W eps mu lambda c rho)
    {v : List (GGT.RelLetter G Lambda)} (hv : v ∈ W) (k n : ℕ) :
    IsLambdaCQuasiGeodesicWord D lambda c (RelWord.revInv ((v.rotate k).take n)) := by
  have hsplit : RelWord.revInv ((v.rotate k).drop n) ++ RelWord.revInv ((v.rotate k).take n)
      ++ [] = RelWord.revInv (v.rotate k) := by
    rw [List.append_nil]
    simp only [RelWord.revInv]
    rw [← List.reverse_append, ← List.map_append, List.take_append_drop]
  have hmem : RelWord.revInv ((v.rotate k).drop n) ++ RelWord.revInv ((v.rotate k).take n)
      ++ [] ∈ W := by
    rw [hsplit]
    exact hcond.inv_mem _ (hcond.rotate_mem v hv k)
  exact isLambdaCQuasiGeodesicWord_of_infix_mem hcond hmem

end QuasiGeodesic

end CutSections

/-! ## Sections from parts -/

/-- **Sections from parts.**  A boundary word that is the concatenation of
`1 ≤ r ≤ 4` quasi-geodesic parts carries `SectionCuts` whose sections are these
parts, in order. -/
def SectionCuts.ofParts {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {lambda c : ℝ} {word : List (GGT.RelLetter G Lambda)}
    (parts : List (List (GGT.RelLetter G Lambda))) (hword : word = parts.flatten)
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hquasi : ∀ part ∈ parts, IsLambdaCQuasiGeodesicWord D lambda c part) :
    SectionCuts D lambda c word where
  count := parts.length
  count_pos := hpos
  count_le := hle
  cut := fun k => CutSections.partsCut parts k
  cut_zero := by simp [CutSections.partsCut]
  cut_last := by
    show CutSections.partsCut parts parts.length = word.length
    rw [CutSections.partsCut_length, hword]
  cut_mono := by
    intro a b hab
    exact CutSections.partsCut_mono parts (Fin.le_def.mp hab)
  quasiGeodesic := by
    intro j
    have hj : (j : ℕ) < parts.length := j.isLt
    show IsLambdaCQuasiGeodesicWord D lambda c
      ((word.drop (CutSections.partsCut parts (j.castSucc : ℕ))).take
        (CutSections.partsCut parts (j.succ : ℕ) - CutSections.partsCut parts (j.castSucc : ℕ)))
    rw [Fin.coe_castSucc, Fin.val_succ, CutSections.partsCut_succ parts hj,
      Nat.add_sub_cancel_left, hword, CutSections.flatten_drop_partsCut_take parts hj]
    exact hquasi _ (List.getElem_mem hj)

theorem SectionCuts.ofParts_count {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {lambda c : ℝ} {word : List (GGT.RelLetter G Lambda)}
    (parts : List (List (GGT.RelLetter G Lambda))) (hword : word = parts.flatten)
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hquasi : ∀ part ∈ parts, IsLambdaCQuasiGeodesicWord D lambda c part) :
    (SectionCuts.ofParts parts hword hpos hle hquasi).count = parts.length :=
  rfl

/-- The length of section `j` of `SectionCuts.ofParts` is the length of part `j`. -/
theorem SectionCuts.ofParts_cut_sub {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {lambda c : ℝ} {word : List (GGT.RelLetter G Lambda)}
    (parts : List (List (GGT.RelLetter G Lambda))) (hword : word = parts.flatten)
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hquasi : ∀ part ∈ parts, IsLambdaCQuasiGeodesicWord D lambda c part)
    (j : Fin (SectionCuts.ofParts parts hword hpos hle hquasi).count) :
    (SectionCuts.ofParts parts hword hpos hle hquasi).cut j.succ
        - (SectionCuts.ofParts parts hword hpos hle hquasi).cut j.castSucc
      = (parts.get (j.cast (SectionCuts.ofParts_count parts hword hpos hle hquasi))).length := by
  have hj : (j : ℕ) < parts.length := j.isLt
  show CutSections.partsCut parts (j.succ : ℕ) - CutSections.partsCut parts (j.castSucc : ℕ) = _
  rw [Fin.coe_castSucc, Fin.val_succ, CutSections.partsCut_succ parts hj,
    Nat.add_sub_cancel_left]
  simp [List.get_eq_getElem]

/-- Section `j` of `SectionCuts.ofParts` is part `j`. -/
theorem SectionCuts.ofParts_part {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {lambda c : ℝ} {word : List (GGT.RelLetter G Lambda)}
    (parts : List (List (GGT.RelLetter G Lambda))) (hword : word = parts.flatten)
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hquasi : ∀ part ∈ parts, IsLambdaCQuasiGeodesicWord D lambda c part)
    (j : Fin (SectionCuts.ofParts parts hword hpos hle hquasi).count) :
    (SectionCuts.ofParts parts hword hpos hle hquasi).part j
      = parts.get (j.cast (SectionCuts.ofParts_count parts hword hpos hle hquasi)) := by
  subst hword
  have hj : (j : ℕ) < parts.length := j.isLt
  show (parts.flatten.drop (CutSections.partsCut parts (j.castSucc : ℕ))).take
      (CutSections.partsCut parts (j.succ : ℕ) - CutSections.partsCut parts (j.castSucc : ℕ))
      = _
  rw [Fin.coe_castSucc, Fin.val_succ, CutSections.partsCut_succ parts hj,
    Nat.add_sub_cancel_left, CutSections.flatten_drop_partsCut_take parts hj]
  simp [List.get_eq_getElem]

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CutSections.flatten_drop_partsCut_take
#audit_axioms GroupApproximation.GGT.VanKampen.CutSections.isLambdaCQuasiGeodesicWord_infix
#audit_axioms GroupApproximation.GGT.VanKampen.CutSections.isLambdaCQuasiGeodesicWord_drop_take
#audit_axioms GroupApproximation.GGT.VanKampen.CutSections.wordDist_vertex_le
#audit_axioms GroupApproximation.GGT.VanKampen.CutSections.c_nonneg_of_isLambdaCQuasiGeodesicWord
#audit_axioms GroupApproximation.GGT.VanKampen.CutSections.sub_one_mul_le_of_isLambdaCQuasiGeodesicWord
#audit_axioms GroupApproximation.GGT.VanKampen.CutSections.isLambdaCQuasiGeodesicWord_of_geodesic
#audit_axioms GroupApproximation.GGT.VanKampen.CutSections.isLambdaCQuasiGeodesicWord_of_infix_mem
#audit_axioms GroupApproximation.GGT.VanKampen.CutSections.isLambdaCQuasiGeodesicWord_rotate_take
#audit_axioms GroupApproximation.GGT.VanKampen.CutSections.isLambdaCQuasiGeodesicWord_revInv_rotate_take
#audit_axioms GroupApproximation.GGT.VanKampen.SectionCuts.ofParts
#audit_axioms GroupApproximation.GGT.VanKampen.SectionCuts.ofParts_cut_sub
#audit_axioms GroupApproximation.GGT.VanKampen.SectionCuts.ofParts_part
