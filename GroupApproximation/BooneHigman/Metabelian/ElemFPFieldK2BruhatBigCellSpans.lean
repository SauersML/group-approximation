import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatStatement
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2Finite
import GroupApproximation.Meta.AxiomGuard

/-!
# Big Bruhat cell, part 1: the root spans and how they normalize each other

Lane `bh-met-64c`.  This file fixes `L ∉ K` and names the root spans used in the proof of
`BruhatBigCellStatement`:

* `S = G_K = ⟨x_ij : i, j ∈ K⟩`,
* `U = ⟨x_iL : i ∈ K⟩` (column `L`), and `U_{≠b}` (column `L`, rows `≠ b`),
* `V = ⟨x_Lj : j ∈ K⟩` (row `L`), and `V_{≠j₀}` (row `L`, columns `≠ j₀`),
* `C_b = ⟨x_kb : k ∈ K ∪ {L}⟩` (column `b`).

Proof route: each normalization lemma is `rootSpan_normalizes`, with the generator case
coming from `conj_x_left` / `conj_x_right` (an adjacent pair) or `x_commute_of_ne` otherwise.

* `S` normalizes `V`: `x_ij(a) x_Li(b) x_ij(a)⁻¹ = x_Li(b) x_Lj(-ba)`.
* `S` normalizes `U`: `x_ij(a) x_jL(b) x_ij(a)⁻¹ = x_iL(ab) x_jL(b)`.
* `U_{≠b}` normalizes `C_b`: `x_iL(t) x_Lb(a) x_iL(t)⁻¹ = x_ib(ta) x_Lb(a)`.

`bruhatBigCell_third` extracts a third index from `3 ≤ |I|`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (conj_x_left conj_x_right
  conj_of_commute)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  x_mem_rootSpan rootSpan_normalizes)

/-- A third index avoiding two given ones, when `3 ≤ |I|`. -/
theorem bruhatBigCell_third {I : Type*} [Fintype I] [DecidableEq I]
    (hI : 3 ≤ Fintype.card I) (a b : I) : ∃ k, a ≠ k ∧ b ≠ k := by
  have hcard : 0 < ((Finset.univ.erase a).erase b).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase a) (a := b)
    have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset I)) (a := a)
    rw [Finset.card_univ] at h2
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hcard
  refine ⟨k, fun e => ?_, fun e => ?_⟩
  · subst e
    simp at hk
  · subst e
    simp at hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_third

/-- An index of `K` differs from `L ∉ K`. -/
theorem bruhatBigCell_ne {I : Type*} {K : Finset I} {L j : I} (hLK : L ∉ K) (hj : j ∈ K) :
    j ≠ L := fun e => hLK (e ▸ hj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_ne

section Spans

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- `S = G_K`. -/
abbrev bruhatBigCellS (R : Type*) [Field R] (K : Finset I) : Subgroup (SteinbergGroup I R) :=
  rootSpan (R := R) (fun i j => i ∈ K ∧ j ∈ K)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCellS

/-- `U = ⟨x_iL : i ∈ K⟩`. -/
abbrev bruhatBigCellU (R : Type*) [Field R] (K : Finset I) (L : I) :
    Subgroup (SteinbergGroup I R) :=
  rootSpan (R := R) (fun i j => j = L ∧ i ∈ K)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCellU

/-- `V = ⟨x_Lj : j ∈ K⟩`. -/
abbrev bruhatBigCellV (R : Type*) [Field R] (K : Finset I) (L : I) :
    Subgroup (SteinbergGroup I R) :=
  rootSpan (R := R) (fun i j => i = L ∧ j ∈ K)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCellV

/-- `U_{≠b} = ⟨x_iL : i ∈ K, i ≠ b⟩`. -/
abbrev bruhatBigCellUex (R : Type*) [Field R] (K : Finset I) (L b : I) :
    Subgroup (SteinbergGroup I R) :=
  rootSpan (R := R) (fun i j => j = L ∧ i ∈ K ∧ i ≠ b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCellUex

/-- `V_{≠j₀} = ⟨x_Lj : j ∈ K, j ≠ j₀⟩`. -/
abbrev bruhatBigCellVex (R : Type*) [Field R] (K : Finset I) (L j₀ : I) :
    Subgroup (SteinbergGroup I R) :=
  rootSpan (R := R) (fun i j => i = L ∧ j ∈ K ∧ j ≠ j₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCellVex

/-- `C_b = ⟨x_kb : k ∈ K ∪ {L}⟩`. -/
abbrev bruhatBigCellC (R : Type*) [Field R] (K : Finset I) (L b : I) :
    Subgroup (SteinbergGroup I R) :=
  rootSpan (R := R) (fun i j => j = b ∧ i ∈ insert L K)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCellC

end Spans

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

theorem bruhatBigCell_x_mem_S {K : Finset I} {i j : I} (hij : i ≠ j) (a : R) (hi : i ∈ K)
    (hj : j ∈ K) : x i j hij a ∈ bruhatBigCellS R K :=
  x_mem_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) hij a ⟨hi, hj⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_x_mem_S

theorem bruhatBigCell_x_mem_U {K : Finset I} {L i : I} (hiL : i ≠ L) (a : R) (hi : i ∈ K) :
    x i L hiL a ∈ bruhatBigCellU R K L :=
  x_mem_rootSpan (p := fun i j => j = L ∧ i ∈ K) hiL a ⟨rfl, hi⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_x_mem_U

theorem bruhatBigCell_x_mem_V {K : Finset I} {L j : I} (hLj : L ≠ j) (a : R) (hj : j ∈ K) :
    x L j hLj a ∈ bruhatBigCellV R K L :=
  x_mem_rootSpan (p := fun i j => i = L ∧ j ∈ K) hLj a ⟨rfl, hj⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_x_mem_V

theorem bruhatBigCell_x_mem_Uex {K : Finset I} {L b i : I} (hiL : i ≠ L) (a : R)
    (hi : i ∈ K) (hib : i ≠ b) : x i L hiL a ∈ bruhatBigCellUex R K L b :=
  x_mem_rootSpan (p := fun i j => j = L ∧ i ∈ K ∧ i ≠ b) hiL a ⟨rfl, hi, hib⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_x_mem_Uex

theorem bruhatBigCell_x_mem_Vex {K : Finset I} {L j₀ j : I} (hLj : L ≠ j) (a : R)
    (hj : j ∈ K) (hjj : j ≠ j₀) : x L j hLj a ∈ bruhatBigCellVex R K L j₀ :=
  x_mem_rootSpan (p := fun i j => i = L ∧ j ∈ K ∧ j ≠ j₀) hLj a ⟨rfl, hj, hjj⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_x_mem_Vex

theorem bruhatBigCell_x_mem_C {K : Finset I} {L b k : I} (hkb : k ≠ b) (a : R)
    (hk : k ∈ insert L K) : x k b hkb a ∈ bruhatBigCellC R K L b :=
  x_mem_rootSpan (p := fun i j => j = b ∧ i ∈ insert L K) hkb a ⟨rfl, hk⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_x_mem_C

/-- `S` normalizes `V`. -/
theorem bruhatBigCell_S_conj_V {K : Finset I} {L : I} (hLK : L ∉ K)
    {s : SteinbergGroup I R} (hs : s ∈ bruhatBigCellS R K)
    {v : SteinbergGroup I R} (hv : v ∈ bruhatBigCellV R K L) :
    s * v * s⁻¹ ∈ bruhatBigCellV R K L := by
  refine rootSpan_normalizes (p := fun i j => i ∈ K ∧ j ∈ K) (q := fun i j => i = L ∧ j ∈ K)
    ?_ hs hv
  intro i j hij a hp k l hkl b hq
  obtain ⟨_, hj⟩ := hp
  obtain ⟨hk, hl⟩ := hq
  subst k
  by_cases hli : l = i
  · subst l
    rw [conj_x_right L i j hkl hij (bruhatBigCell_ne hLK hj).symm b a]
    exact Subgroup.mul_mem _ (bruhatBigCell_x_mem_V hkl b hl)
      (bruhatBigCell_x_mem_V (bruhatBigCell_ne hLK hj).symm _ hj)
  · rw [conj_of_commute (x_commute_of_ne i j L l hij hkl (bruhatBigCell_ne hLK hj) hli a b)]
    exact bruhatBigCell_x_mem_V hkl b hl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_S_conj_V

/-- `S` normalizes `U`. -/
theorem bruhatBigCell_S_conj_U {K : Finset I} {L : I} (hLK : L ∉ K)
    {s : SteinbergGroup I R} (hs : s ∈ bruhatBigCellS R K)
    {u : SteinbergGroup I R} (hu : u ∈ bruhatBigCellU R K L) :
    s * u * s⁻¹ ∈ bruhatBigCellU R K L := by
  refine rootSpan_normalizes (p := fun i j => i ∈ K ∧ j ∈ K) (q := fun i j => j = L ∧ i ∈ K)
    ?_ hs hu
  intro i j hij a hp k l hkl b hq
  obtain ⟨hi, _⟩ := hp
  obtain ⟨hl, hk⟩ := hq
  subst l
  by_cases hkj : k = j
  · subst k
    rw [conj_x_left i j L hij hkl (bruhatBigCell_ne hLK hi) a b]
    exact Subgroup.mul_mem _ (bruhatBigCell_x_mem_U (bruhatBigCell_ne hLK hi) _ hi)
      (bruhatBigCell_x_mem_U hkl b hk)
  · rw [conj_of_commute (x_commute_of_ne i j k L hij hkl (Ne.symm hkj)
      (bruhatBigCell_ne hLK hi).symm a b)]
    exact bruhatBigCell_x_mem_U hkl b hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_S_conj_U

/-- `U_{≠b}` normalizes `C_b`. -/
theorem bruhatBigCell_Uex_conj_C {K : Finset I} {L b : I}
    {u : SteinbergGroup I R} (hu : u ∈ bruhatBigCellUex R K L b)
    {y : SteinbergGroup I R} (hy : y ∈ bruhatBigCellC R K L b) :
    u * y * u⁻¹ ∈ bruhatBigCellC R K L b := by
  refine rootSpan_normalizes (p := fun i j => j = L ∧ i ∈ K ∧ i ≠ b)
    (q := fun i j => j = b ∧ i ∈ insert L K) ?_ hu hy
  intro i j hij a hp k l hkl c hq
  obtain ⟨hjL, hi, hib⟩ := hp
  obtain ⟨hlb, hk⟩ := hq
  subst j
  subst l
  by_cases hkL : k = L
  · subst k
    rw [conj_x_left i L b hij hkl hib a c]
    exact Subgroup.mul_mem _ (bruhatBigCell_x_mem_C hib _ (Finset.mem_insert_of_mem hi))
      (bruhatBigCell_x_mem_C hkl c hk)
  · rw [conj_of_commute (x_commute_of_ne i L k b hij hkl (Ne.symm hkL) (Ne.symm hib) a c)]
    exact bruhatBigCell_x_mem_C hkl c hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_Uex_conj_C

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
