import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKAdd

/-!
# vdK 3.13–3.15: the sets `X̄(i, j)` (k2-poly, piece F.1)

W. van der Kallen, *Another presentation for Steinberg groups*, Indag. Math. **39** (1977),
3.13–3.15. Throughout, `4 ≤ n = |I|`.

* `basicRow i p q = i_q ε_pᵀ - i_p ε_qᵀ`; `IsBasic i w`: `w` is a scalar multiple of one.
* `Xbar i j` (**vdK 3.13**): the products `∏ₘ x(i, wᵐ)` with `Σₘ wᵐ = j` and every `wᵐ` basic.
  `mul_mem_Xbar`: `X̄(i, j) X̄(i, k) ⊆ X̄(i, j + k)`; `stU_of_mem_Xbar`: `π = e(i, j)` on `X̄(i, j)`.
* `conj_mem_Xbar` (**vdK 3.14**): `y X̄(i, j) y⁻¹ ⊆ X̄(π(y) i, j π(y)⁻¹)` for every `y ∈ St`.
  For a generator `y = x_pq(a)` this is vdK 3.12 (`conj_xz_x`), followed by 3.11 (`xz_add`) when
  `j π(y)⁻¹` is a sum of two basic rows for the new column (`basic_conj_mem`).
* `Xbar_subsingleton` (**vdK 3.15**): `X̄(M ε_r, j)` has at most one element for `M ∈ π(St)`. For
  `M = 1` every element is `x_r(j)` (`eq_rowProd_of_mem_Xbar_single`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace VdK

open scoped commutatorElement Matrix
open GroupApproximation.SteinbergGroup

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

/-! ### Counting and generation -/

omit [DecidableEq I] in
theorem exists_ne_three (h4 : 4 ≤ Fintype.card I) (a b c : I) :
    ∃ t, t ≠ a ∧ t ≠ b ∧ t ≠ c := by
  classical
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset I) ⊆ {a, b, c} := by
    intro t _
    by_cases hta : t = a
    · simp [hta]
    by_cases htb : t = b
    · simp [htb]
    simp [h t hta htb]
  have h1 := Finset.card_insert_le a (insert b ({c} : Finset I))
  have h2 := Finset.card_insert_le b ({c} : Finset I)
  have h3 := Finset.card_singleton c
  have h5 := Finset.card_le_card hsub
  rw [Finset.card_univ] at h5
  omega

variable (I A) in
/-- The generators `x_pq(a)` generate `St(n, A)`. -/
theorem closure_x :
    Subgroup.closure {g : SteinbergGroup I A | ∃ (p q : I) (hpq : p ≠ q) (a : A), x p q hpq a = g} =
      ⊤ := by
  rw [← PresentedGroup.closure_range_of (SteinbergGroup.relations (I := I) (R := A))]
  congr 1
  ext g
  constructor
  · rintro ⟨p, q, hpq, a, rfl⟩
    exact ⟨⟨p, q, hpq, a⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    rcases e with ⟨p, q, hpq, a⟩
    exact ⟨p, q, hpq, a, rfl⟩

/-! ### Basic rows -/

/-- `i_q ε_pᵀ - i_p ε_qᵀ` (vdK 3.1, 3.13). -/
def basicRow (i : I → A) (p q : I) : I → A :=
  i q • Pi.single p (1 : A) - i p • Pi.single q (1 : A)

theorem basicRow_dotProduct (i : I → A) (p q : I) : basicRow i p q ⬝ᵥ i = 0 := by
  simp only [basicRow, sub_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
  ring

theorem smul_basicRow_dotProduct (i : I → A) (c : A) (p q : I) :
    (c • basicRow i p q) ⬝ᵥ i = 0 := by
  rw [smul_dotProduct, basicRow_dotProduct, smul_zero]

omit [Fintype I] in
theorem basicRow_apply_of_ne (i : I → A) {p q t : I} (htp : t ≠ p) (htq : t ≠ q) :
    basicRow i p q t = 0 := by
  rw [basicRow, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne htp,
    Pi.single_eq_of_ne htq, smul_zero, smul_zero, sub_zero]

omit [Fintype I] in
theorem smul_basicRow_apply_of_ne (i : I → A) (c : A) {p q t : I} (htp : t ≠ p) (htq : t ≠ q) :
    (c • basicRow i p q) t = 0 := by
  rw [Pi.smul_apply, basicRow_apply_of_ne i htp htq, smul_zero]

omit [Fintype I] in
theorem basicRow_apply_left (i : I → A) {p q : I} (hpq : p ≠ q) : basicRow i p q p = i q := by
  rw [basicRow, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hpq, smul_zero, smul_eq_mul, mul_one, sub_zero]

omit [Fintype I] in
theorem basicRow_apply_right (i : I → A) {p q : I} (hpq : p ≠ q) : basicRow i p q q = -i p := by
  rw [basicRow, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hpq.symm, smul_zero, smul_eq_mul, mul_one, zero_sub]

omit [Fintype I] in
theorem basicRow_self (i : I → A) (p : I) : basicRow i p p = 0 := by
  rw [basicRow, sub_self]

omit [Fintype I] in
/-- The `r`-th coordinate of a basic row for `ε_r` vanishes. -/
theorem basicRow_single_apply_self (r p q : I) : basicRow (Pi.single r (1 : A)) p q r = 0 := by
  simp only [basicRow, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hq : q = r
  · by_cases hp : p = r
    · simp [hq, hp]
    · simp [hq, hp, Ne.symm hp]
  · by_cases hp : p = r
    · simp [hq, hp, Ne.symm hq]
    · simp [hp, hq, Ne.symm hp, Ne.symm hq]

omit [Fintype I] in
theorem single_eq_smul_one (q : I) (b : A) : Pi.single q b = b • Pi.single q (1 : A) := by
  rw [← Pi.single_smul', smul_eq_mul, mul_one]

omit [Fintype I] in
theorem add_single_apply_self (i : I → A) (p : I) (b : A) : (i + Pi.single p b) p = i p + b := by
  rw [Pi.add_apply, Pi.single_eq_same]

omit [Fintype I] in
theorem add_single_apply_of_ne (i : I → A) {p t : I} (htp : t ≠ p) (b : A) :
    (i + Pi.single p b) t = i t := by
  rw [Pi.add_apply, Pi.single_eq_of_ne htp, add_zero]

omit [Fintype I] in
theorem basicRow_add_single_of_ne (i : I → A) {p r s : I} (hpr : p ≠ r) (hps : p ≠ s) (b : A) :
    basicRow (i + Pi.single p b) r s = basicRow i r s := by
  rw [basicRow, basicRow, add_single_apply_of_ne i (Ne.symm hpr), add_single_apply_of_ne i (Ne.symm hps)]

/-- `w` is a scalar multiple of a basic row for `i`. -/
def IsBasic (i w : I → A) : Prop :=
  ∃ (c : A) (p q : I), w = c • basicRow i p q

theorem IsBasic.dotProduct {i w : I → A} (h : IsBasic i w) : w ⬝ᵥ i = 0 := by
  obtain ⟨c, p, q, rfl⟩ := h
  exact smul_basicRow_dotProduct i c p q

omit [DecidableEq I] in
theorem exists_two_ne_of_card (h4 : 4 ≤ Fintype.card I) (p q : I) :
    ∃ r s : I, r ≠ s ∧ r ≠ p ∧ r ≠ q ∧ s ≠ p ∧ s ≠ q := by
  obtain ⟨r, hrp, hrq, -⟩ := exists_ne_three h4 p q p
  obtain ⟨s, hsp, hsq, hsr⟩ := exists_ne_three h4 p q r
  exact ⟨r, s, Ne.symm hsr, hrp, hrq, hsp, hsq⟩

theorem IsBasic.exists_two_zeros (h4 : 4 ≤ Fintype.card I) {i w : I → A} (h : IsBasic i w) :
    ∃ r s : I, r ≠ s ∧ w r = 0 ∧ w s = 0 := by
  obtain ⟨c, p, q, rfl⟩ := h
  obtain ⟨r, s, hrs, hrp, hrq, hsp, hsq⟩ := exists_two_ne_of_card h4 p q
  exact ⟨r, s, hrs, smul_basicRow_apply_of_ne i c hrp hrq, smul_basicRow_apply_of_ne i c hsp hsq⟩

theorem stU_xz_of_basic (h4 : 4 ≤ Fintype.card I) {i w : I → A} (h : IsBasic i w) :
    stU I A (xz i w) = eUnit i w h.dotProduct := by
  obtain ⟨r, -, -, hwr, -⟩ := h.exists_two_zeros h4
  exact stU_xz h.dotProduct hwr

/-! ### The sets `X̄(i, j)` -/

/-- **vdK 3.13.** `X̄(i, j)`: the products `∏ₘ x(i, wᵐ)`, in any order, with `Σₘ wᵐ = j` and
every `wᵐ` a scalar multiple of a basic row for `i`. -/
def Xbar (i j : I → A) : Set (SteinbergGroup I A) :=
  {g | ∃ L : List (I → A), (∀ w ∈ L, IsBasic i w) ∧ L.sum = j ∧ (L.map (xz i)).prod = g}

theorem mem_Xbar {i j : I → A} {g : SteinbergGroup I A} :
    g ∈ Xbar i j ↔
      ∃ L : List (I → A), (∀ w ∈ L, IsBasic i w) ∧ L.sum = j ∧ (L.map (xz i)).prod = g :=
  Iff.rfl

theorem one_mem_Xbar (i : I → A) : (1 : SteinbergGroup I A) ∈ Xbar i 0 :=
  mem_Xbar.2 ⟨[], by simp, rfl, rfl⟩

theorem xz_mem_Xbar {i w : I → A} (hw : IsBasic i w) : xz i w ∈ Xbar i w :=
  mem_Xbar.2 ⟨[w], by simpa using hw, by simp, by simp⟩

theorem mul_mem_Xbar {i j k : I → A} {g h : SteinbergGroup I A} (hg : g ∈ Xbar i j)
    (hh : h ∈ Xbar i k) : g * h ∈ Xbar i (j + k) := by
  obtain ⟨L, hL, rfl, rfl⟩ := hg
  obtain ⟨M, hM, rfl, rfl⟩ := hh
  refine mem_Xbar.2 ⟨L ++ M, fun w hw => ?_, List.sum_append, by
    rw [List.map_append, List.prod_append]⟩
  rcases List.mem_append.1 hw with hw | hw
  · exact hL w hw
  · exact hM w hw

theorem dotProduct_of_mem_Xbar {i j : I → A} {g : SteinbergGroup I A} (hg : g ∈ Xbar i j) :
    j ⬝ᵥ i = 0 := by
  obtain ⟨L, hL, rfl, -⟩ := hg
  induction L with
  | nil => exact zero_dotProduct i
  | cons w L ih =>
    rw [List.sum_cons, add_dotProduct, (hL w (List.mem_cons.2 (Or.inl rfl))).dotProduct,
      ih (fun w' h' => hL w' (List.mem_cons.2 (Or.inr h'))), add_zero]

theorem stU_list_prod (h4 : 4 ≤ Fintype.card I) (i : I → A) (L : List (I → A))
    (hL : ∀ w ∈ L, IsBasic i w) (h : L.sum ⬝ᵥ i = 0) :
    stU I A (L.map (xz i)).prod = eUnit i L.sum h := by
  induction L with
  | nil =>
    rw [List.map_nil, List.prod_nil, map_one]
    exact (eUnit_zero_right i h).symm
  | cons w L ih =>
    have hw : IsBasic i w := hL w (List.mem_cons.2 (Or.inl rfl))
    have hL' : ∀ w' ∈ L, IsBasic i w' := fun w' h' => hL w' (List.mem_cons.2 (Or.inr h'))
    have hLi : L.sum ⬝ᵥ i = 0 := dotProduct_of_mem_Xbar (mem_Xbar.2 ⟨L, hL', rfl, rfl⟩)
    rw [List.map_cons, List.prod_cons, map_mul, stU_xz_of_basic h4 hw, ih hL' hLi]
    exact eUnit_mul i w L.sum hw.dotProduct hLi h

/-- `π = e(i, j)` on `X̄(i, j)`. -/
theorem stU_of_mem_Xbar (h4 : 4 ≤ Fintype.card I) {i j : I → A} {g : SteinbergGroup I A}
    (hg : g ∈ Xbar i j) (h : j ⬝ᵥ i = 0) : stU I A g = eUnit i j h := by
  obtain ⟨L, hL, rfl, rfl⟩ := hg
  exact stU_list_prod h4 i L hL h

/-! ### vdK 3.14 -/

/-- Case `p ∉ {r, s}` of `basic_conj_mem`: the row does not change and stays basic. -/
theorem basic_conj_mem_a {p q r s : I} (a c : A) (i : I → A) (hpr : p ≠ r) (hps : p ≠ s) :
    xz (i + Pi.single p (i q * a))
        (c • basicRow i r s - Pi.single q ((c • basicRow i r s) p * a)) ∈
      Xbar (i + Pi.single p (i q * a))
        (c • basicRow i r s - Pi.single q ((c • basicRow i r s) p * a)) := by
  rw [smul_basicRow_apply_of_ne i c hpr hps, zero_mul, Pi.single_zero, sub_zero,
    ← basicRow_add_single_of_ne i hpr hps (i q * a)]
  exact xz_mem_Xbar ⟨c, r, s, rfl⟩

/-- Case `(r, s) = (p, q)` of `basic_conj_mem`. -/
theorem basic_conj_mem_b1 {p q : I} (hpq : p ≠ q) (a c : A) (i : I → A) :
    xz (i + Pi.single p (i q * a))
        (c • basicRow i p q - Pi.single q ((c • basicRow i p q) p * a)) ∈
      Xbar (i + Pi.single p (i q * a))
        (c • basicRow i p q - Pi.single q ((c • basicRow i p q) p * a)) := by
  have hw : c • basicRow i p q - Pi.single q ((c • basicRow i p q) p * a) =
      c • basicRow (i + Pi.single p (i q * a)) p q := by
    rw [Pi.smul_apply, smul_eq_mul, basicRow_apply_left i hpq]
    simp only [basicRow]
    rw [add_single_apply_of_ne i hpq.symm, add_single_apply_self, single_eq_smul_one q (c * i q * a)]
    module
  rw [hw]
  exact xz_mem_Xbar ⟨c, p, q, rfl⟩

/-- Case `r = p`, `s ≠ q` of `basic_conj_mem`: the row splits into two basic rows. -/
theorem basic_conj_mem_b2 (h4 : 4 ≤ Fintype.card I) {p q s : I} (hpq : p ≠ q) (hps : p ≠ s)
    (hqs : q ≠ s) (a c : A) (i : I → A) :
    xz (i + Pi.single p (i q * a))
        (c • basicRow i p s - Pi.single q ((c • basicRow i p s) p * a)) ∈
      Xbar (i + Pi.single p (i q * a))
        (c • basicRow i p s - Pi.single q ((c • basicRow i p s) p * a)) := by
  have hw : c • basicRow i p s - Pi.single q ((c • basicRow i p s) p * a) =
      c • basicRow (i + Pi.single p (i q * a)) p s +
        (c * a) • basicRow (i + Pi.single p (i q * a)) s q := by
    rw [Pi.smul_apply, smul_eq_mul, basicRow_apply_left i hps]
    simp only [basicRow]
    rw [add_single_apply_of_ne i (Ne.symm hps), add_single_apply_self,
      add_single_apply_of_ne i (Ne.symm hpq), single_eq_smul_one q (c * i s * a)]
    module
  obtain ⟨t, htp, hts, htq⟩ := exists_ne_three h4 p s q
  rw [hw, ← xz_add (p := t) (q := p) (r := q) (Ne.symm htq) (Ne.symm htp)
    (smul_basicRow_dotProduct _ c p s) (smul_basicRow_dotProduct _ (c * a) s q)
    (smul_basicRow_apply_of_ne _ c htp hts) (smul_basicRow_apply_of_ne _ c (Ne.symm hpq) hqs)
    (smul_basicRow_apply_of_ne _ (c * a) hts htq) (smul_basicRow_apply_of_ne _ (c * a) hps hpq)]
  exact mul_mem_Xbar (xz_mem_Xbar ⟨c, p, s, rfl⟩) (xz_mem_Xbar ⟨c * a, s, q, rfl⟩)

/-- Case `(r, s) = (q, p)` of `basic_conj_mem`. -/
theorem basic_conj_mem_c1 {p q : I} (hpq : p ≠ q) (a c : A) (i : I → A) :
    xz (i + Pi.single p (i q * a))
        (c • basicRow i q p - Pi.single q ((c • basicRow i q p) p * a)) ∈
      Xbar (i + Pi.single p (i q * a))
        (c • basicRow i q p - Pi.single q ((c • basicRow i q p) p * a)) := by
  have hw : c • basicRow i q p - Pi.single q ((c • basicRow i q p) p * a) =
      c • basicRow (i + Pi.single p (i q * a)) q p := by
    rw [Pi.smul_apply, smul_eq_mul, basicRow_apply_right i hpq.symm]
    simp only [basicRow]
    rw [add_single_apply_of_ne i hpq.symm, add_single_apply_self,
      single_eq_smul_one q (c * -i q * a)]
    module
  rw [hw]
  exact xz_mem_Xbar ⟨c, q, p, rfl⟩

/-- Case `s = p`, `r ≠ q` of `basic_conj_mem`: the row splits into two basic rows. -/
theorem basic_conj_mem_c2 (h4 : 4 ≤ Fintype.card I) {p q r : I} (hpq : p ≠ q) (hrp : r ≠ p)
    (hqr : q ≠ r) (a c : A) (i : I → A) :
    xz (i + Pi.single p (i q * a))
        (c • basicRow i r p - Pi.single q ((c • basicRow i r p) p * a)) ∈
      Xbar (i + Pi.single p (i q * a))
        (c • basicRow i r p - Pi.single q ((c • basicRow i r p) p * a)) := by
  have hw : c • basicRow i r p - Pi.single q ((c • basicRow i r p) p * a) =
      c • basicRow (i + Pi.single p (i q * a)) r p +
        (c * a) • basicRow (i + Pi.single p (i q * a)) q r := by
    rw [Pi.smul_apply, smul_eq_mul, basicRow_apply_right i hrp]
    simp only [basicRow]
    rw [add_single_apply_self, add_single_apply_of_ne i hrp, add_single_apply_of_ne i hpq.symm,
      single_eq_smul_one q (c * -i r * a)]
    module
  obtain ⟨t, htr, htp, htq⟩ := exists_ne_three h4 r p q
  rw [hw, ← xz_add (p := t) (q := p) (r := q) (Ne.symm htq) (Ne.symm htp)
    (smul_basicRow_dotProduct _ c r p) (smul_basicRow_dotProduct _ (c * a) q r)
    (smul_basicRow_apply_of_ne _ c htr htp) (smul_basicRow_apply_of_ne _ c hqr hpq.symm)
    (smul_basicRow_apply_of_ne _ (c * a) htq htr) (smul_basicRow_apply_of_ne _ (c * a) hpq hrp.symm)]
  exact mul_mem_Xbar (xz_mem_Xbar ⟨c, r, p, rfl⟩) (xz_mem_Xbar ⟨c * a, q, r, rfl⟩)

/-- **vdK 3.14 for a generator and one basic row.** If `w` is basic for `i`, then
`x(π i, w π⁻¹) ∈ X̄(π i, w π⁻¹)` for `π = π(x_pq(a))`. -/
theorem basic_conj_mem (h4 : 4 ≤ Fintype.card I) {p q : I} (hpq : p ≠ q) (a : A) (i : I → A)
    {w : I → A} (hw : IsBasic i w) :
    xz ((1 + Matrix.single p q a) *ᵥ i) (w ᵥ* (1 - Matrix.single p q a)) ∈
      Xbar ((1 + Matrix.single p q a) *ᵥ i) (w ᵥ* (1 - Matrix.single p q a)) := by
  rw [one_add_single_mulVec, vecMul_one_sub_single]
  obtain ⟨c, r, s, rfl⟩ := hw
  by_cases hrs : r = s
  · rw [hrs, basicRow_self, smul_zero, Pi.zero_apply, zero_mul, Pi.single_zero, sub_zero, xz_zero]
    exact one_mem_Xbar _
  by_cases hpr : p = r
  · rw [← hpr] at hrs ⊢
    by_cases hqs : q = s
    · rw [← hqs]
      exact basic_conj_mem_b1 hpq a c i
    · exact basic_conj_mem_b2 h4 hpq hrs hqs a c i
  by_cases hps : p = s
  · rw [← hps] at hrs ⊢
    by_cases hqr : q = r
    · rw [← hqr]
      exact basic_conj_mem_c1 hpq a c i
    · exact basic_conj_mem_c2 h4 hpq hrs hqr a c i
  exact basic_conj_mem_a a c i hpr hps

/-- **vdK 3.14 for a generator.** -/
theorem conj_x_mem_Xbar (h4 : 4 ≤ Fintype.card I) {p q : I} (hpq : p ≠ q) (a : A)
    {i j : I → A} {g : SteinbergGroup I A} (hg : g ∈ Xbar i j) :
    x p q hpq a * g * (x p q hpq a)⁻¹ ∈
      Xbar ((1 + Matrix.single p q a) *ᵥ i) (j ᵥ* (1 - Matrix.single p q a)) := by
  obtain ⟨L, hL, rfl, rfl⟩ := hg
  induction L with
  | nil =>
    rw [List.map_nil, List.prod_nil, mul_one, mul_inv_cancel, List.sum_nil, Matrix.zero_vecMul]
    exact one_mem_Xbar _
  | cons w L ih =>
    have hw : IsBasic i w := hL w (List.mem_cons.2 (Or.inl rfl))
    have hL' : ∀ w' ∈ L, IsBasic i w' := fun w' h' => hL w' (List.mem_cons.2 (Or.inr h'))
    have e : x p q hpq a * ((List.map (xz i) (w :: L)).prod) * (x p q hpq a)⁻¹ =
        (x p q hpq a * xz i w * (x p q hpq a)⁻¹) *
          (x p q hpq a * (List.map (xz i) L).prod * (x p q hpq a)⁻¹) := by
      rw [List.map_cons, List.prod_cons]
      group
    rw [e, List.sum_cons, Matrix.add_vecMul]
    refine mul_mem_Xbar ?_ (ih hL')
    obtain ⟨r, s, hrs, hwr, hws⟩ := hw.exists_two_zeros h4
    rw [conj_xz_x hpq a hw.dotProduct hrs hwr hws]
    exact basic_conj_mem h4 hpq a i hw

/-- **vdK 3.14.** `y X̄(i, j) y⁻¹ ⊆ X̄(π(y) i, j π(y)⁻¹)` for every `y ∈ St(n, A)`. -/
theorem conj_mem_Xbar (h4 : 4 ≤ Fintype.card I) (y : SteinbergGroup I A) :
    ∀ {i j : I → A} {g : SteinbergGroup I A}, g ∈ Xbar i j →
      y * g * y⁻¹ ∈ Xbar (mat y *ᵥ i) (j ᵥ* matInv y) := by
  have hy : y ∈ Subgroup.closure
      {g : SteinbergGroup I A | ∃ (p q : I) (hpq : p ≠ q) (a : A), x p q hpq a = g} := by
    rw [closure_x]
    exact Subgroup.mem_top y
  induction hy using Subgroup.closure_induction'' with
  | mem z hz =>
    obtain ⟨p, q, hpq, a, rfl⟩ := hz
    intro i j g hg
    rw [mat_x, matInv_x]
    exact conj_x_mem_Xbar h4 hpq a hg
  | inv_mem z hz =>
    obtain ⟨p, q, hpq, a, rfl⟩ := hz
    intro i j g hg
    rw [← x_neg, mat_x, matInv_x]
    exact conj_x_mem_Xbar h4 hpq (-a) hg
  | one =>
    intro i j g hg
    rw [mat_one, matInv_one, Matrix.one_mulVec, Matrix.vecMul_one, one_mul, inv_one, mul_one]
    exact hg
  | mul z w _ _ hz hw =>
    intro i j g hg
    have h1 := hz (hw hg)
    have e : z * w * g * (z * w)⁻¹ = z * (w * g * w⁻¹) * z⁻¹ := by group
    rw [e, mat_mul, matInv_mul, ← Matrix.mulVec_mulVec, ← Matrix.vecMul_vecMul]
    exact h1

#audit_axioms conj_mem_Xbar

/-! ### vdK 3.15 -/

/-- For `i = ε_r` every factor `x(ε_r, w)` is `x_r(w)`. -/
theorem xz_single_of_basic {r : I} {w : I → A} (hw : IsBasic (Pi.single r 1) w) :
    xz (Pi.single r 1) w = rowProd r w := by
  obtain ⟨c, p, q, rfl⟩ := hw
  have hr : (c • basicRow (Pi.single r (1 : A)) p q) r = 0 := by
    rw [Pi.smul_apply, basicRow_single_apply_self, smul_zero]
  rw [xz_eq (smul_basicRow_dotProduct _ c p q) hr, xvw_single_self, one_smul]

/-- **vdK 3.15 for `M = 1`.** Every element of `X̄(ε_r, j)` is `x_r(j)`. -/
theorem eq_rowProd_of_mem_Xbar_single {r : I} {j : I → A} {g : SteinbergGroup I A}
    (hg : g ∈ Xbar (Pi.single r 1) j) : g = rowProd r j := by
  obtain ⟨L, hL, rfl, rfl⟩ := hg
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, List.sum_nil, rowProd_zero]
  | cons w L ih =>
    rw [List.map_cons, List.prod_cons, List.sum_cons, rowProd_add,
      xz_single_of_basic (hL w (List.mem_cons.2 (Or.inl rfl))),
      ih (fun w' h' => hL w' (List.mem_cons.2 (Or.inr h')))]

/-- **vdK 3.15.** For `y ∈ St(n, A)`, the set `X̄(π(y) ε_r, j)` has at most one element. -/
theorem Xbar_subsingleton (h4 : 4 ≤ Fintype.card I) (y : SteinbergGroup I A) (r : I)
    (j : I → A) : (Xbar (mat y *ᵥ Pi.single r (1 : A)) j).Subsingleton := by
  intro g hg g' hg'
  have e1 := conj_mem_Xbar h4 y⁻¹ hg
  have e2 := conj_mem_Xbar h4 y⁻¹ hg'
  rw [mat_inv, matInv_inv, Matrix.mulVec_mulVec, matInv_mul_mat, Matrix.one_mulVec] at e1 e2
  have h := (eq_rowProd_of_mem_Xbar_single e1).trans (eq_rowProd_of_mem_Xbar_single e2).symm
  exact mul_left_cancel (mul_right_cancel h)

#audit_axioms Xbar_subsingleton

end VdK
end K2Found
end BooneHigmanLinear
end GroupApproximation
