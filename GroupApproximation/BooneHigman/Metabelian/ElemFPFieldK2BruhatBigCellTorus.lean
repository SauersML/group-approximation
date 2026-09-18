import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellSpans
import GroupApproximation.Meta.AxiomGuard

/-!
# Big Bruhat cell, part 2: the torus `h_mL(c)`

Lane `bh-met-64c`.  `BruhatBigCellData` bundles the setup of `BruhatBigCellStatement` over a
field `R`:

* `L ∉ K` and `m ∈ K`,
* a third index for every pair (from `3 ≤ |I|`),
* the torus law `h_mL(c) h_mL(c') = h_mL(c' c)`.

Over `ZMod p` the torus law holds because the Steinberg symbols are trivial
(`symbol_eq_one_zmod`, giving `bruhatBigCell_h_mul_zmod`).

Proof route for the rest of this file:

* `h_mL(c)⁻¹ = h_mL(c⁻¹)`, from the torus law and `h(1) = 1`.
* `h_mL(c)` normalizes `S`: `h_conj_iq`, `h_conj_pi`, `h_conj_pq`.
* `h_mL(c)` normalizes `V`: `h_conj_ji` (the root `x_Lm`, which needs a third index) and
  `h_conj_jq`.
* Moving the first index: `w_bm(1) w_mL(v) w_bm(1)⁻¹ = w_bL(v)` (`w_conj_x_row_j`,
  `w_conj_x_col_j`), and hence `w_bm(1) h_mL(v) w_bm(1)⁻¹ = h_bL(v)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_conj_x_row_j
  w_conj_x_col_j)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  rootSpan_conj_mem)

/-- Over `ZMod p`, `h_ij(c) h_ij(c') = h_ij(c' c)`, because symbols are trivial. -/
theorem bruhatBigCell_h_mul_zmod {I : Type*} [Fintype I] [DecidableEq I] {p : ℕ}
    [Fact p.Prime] (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (c c' : (ZMod p)ˣ) : h i j hij c * h i j hij c' = h i j hij (c' * c) := by
  have e := symbol_eq_one_zmod i j k hij hik hjk c' c
  rw [symbol, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at e
  exact e.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_h_mul_zmod

/-- The data fixed along the proof of the big-cell factorization. -/
structure BruhatBigCellData (I R : Type*) [Fintype I] [DecidableEq I] [Field R] where
  /-- The finset `K`. -/
  K : Finset I
  /-- The extra index `L ∉ K`. -/
  L : I
  /-- The index `m ∈ K` of the torus `h_mL`. -/
  m : I
  hmL : m ≠ L
  hLK : L ∉ K
  hmK : m ∈ K
  third : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k
  torus : ∀ c c' : Rˣ, h m L hmL c * h m L hmL c' = h m L hmL (c' * c)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.BruhatBigCellData

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- `h_mL(c)⁻¹ = h_mL(c⁻¹)`. -/
theorem bruhatBigCell_h_inv (σ : BruhatBigCellData I R) (c : Rˣ) :
    (h σ.m σ.L σ.hmL c)⁻¹ = h σ.m σ.L σ.hmL c⁻¹ := by
  have e : h σ.m σ.L σ.hmL c * h σ.m σ.L σ.hmL c⁻¹ = 1 := by
    rw [σ.torus, inv_mul_cancel, bruhat_h_one]
  exact (eq_inv_of_mul_eq_one_right e).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_h_inv

/-- `h_mL(c)` normalizes `S = G_K`. -/
theorem bruhatBigCell_h_conj_S (σ : BruhatBigCellData I R) (c : Rˣ)
    {s : SteinbergGroup I R} (hs : s ∈ bruhatBigCellS R σ.K) :
    h σ.m σ.L σ.hmL c * s * (h σ.m σ.L σ.hmL c)⁻¹ ∈ bruhatBigCellS R σ.K := by
  refine rootSpan_conj_mem (p := fun i j => i ∈ σ.K ∧ j ∈ σ.K) ?_ hs
  intro i j hij t hp
  obtain ⟨hi, hj⟩ := hp
  have hiL := bruhatBigCell_ne σ.hLK hi
  have hjL := bruhatBigCell_ne σ.hLK hj
  by_cases him : i = σ.m
  · subst i
    rw [h_conj_iq σ.m σ.L j σ.hmL hij hjL.symm c t]
    exact bruhatBigCell_x_mem_S hij _ σ.hmK hj
  · by_cases hjm : j = σ.m
    · subst j
      rw [h_conj_pi σ.m σ.L i σ.hmL hij hiL c t]
      exact bruhatBigCell_x_mem_S hij _ hi σ.hmK
    · rw [h_conj_pq σ.m σ.L i j σ.hmL hij (Ne.symm him) hiL.symm (Ne.symm hjm) hjL.symm c t]
      exact bruhatBigCell_x_mem_S hij _ hi hj

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_h_conj_S

/-- `h_mL(c)` normalizes `V`. -/
theorem bruhatBigCell_h_conj_V (σ : BruhatBigCellData I R) (c : Rˣ)
    {v : SteinbergGroup I R} (hv : v ∈ bruhatBigCellV R σ.K σ.L) :
    h σ.m σ.L σ.hmL c * v * (h σ.m σ.L σ.hmL c)⁻¹ ∈ bruhatBigCellV R σ.K σ.L := by
  refine rootSpan_conj_mem (p := fun i j => i = σ.L ∧ j ∈ σ.K) ?_ hv
  intro i j hij t hp
  obtain ⟨hi, hj⟩ := hp
  subst i
  by_cases hjm : j = σ.m
  · subst j
    obtain ⟨k, hmk, hLk⟩ := σ.third σ.m σ.L
    rw [h_conj_ji σ.m σ.L k σ.hmL hmk hLk c t]
    exact bruhatBigCell_x_mem_V hij _ σ.hmK
  · rw [h_conj_jq σ.m σ.L j σ.hmL (Ne.symm hjm) hij c t]
    exact bruhatBigCell_x_mem_V hij _ hj

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_h_conj_V

/-- Moving the first index of a Weyl element: `w_bm(1) w_mL(v) w_bm(1)⁻¹ = w_bL(v)`. -/
theorem bruhatBigCell_w_first (b m L : I) (hbm : b ≠ m) (hbL : b ≠ L) (hmL : m ≠ L)
    (v : Rˣ) : w b m hbm (1 : Rˣ) * w m L hmL v * (w b m hbm (1 : Rˣ))⁻¹ = w b L hbL v := by
  show w b m hbm (1 : Rˣ) * (x m L hmL (v : R) * x L m hmL.symm (-((v⁻¹ : Rˣ) : R)) *
      x m L hmL (v : R)) * (w b m hbm (1 : Rˣ))⁻¹ =
    x b L hbL (v : R) * x L b hbL.symm (-((v⁻¹ : Rˣ) : R)) * x b L hbL (v : R)
  rw [conj_mul_three, w_conj_x_row_j b m L hbm hbL hmL (1 : Rˣ),
    w_conj_x_col_j b m L hbm hbL.symm hmL.symm (1 : Rˣ), inv_one, Units.val_one, one_mul,
    mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_w_first

/-- Moving the first index of a torus element: `w_bm(1) h_mL(v) w_bm(1)⁻¹ = h_bL(v)`. -/
theorem bruhatBigCell_h_first (b m L : I) (hbm : b ≠ m) (hbL : b ≠ L) (hmL : m ≠ L)
    (v : Rˣ) : w b m hbm (1 : Rˣ) * h m L hmL v * (w b m hbm (1 : Rˣ))⁻¹ = h b L hbL v := by
  show w b m hbm (1 : Rˣ) * (w m L hmL v * w m L hmL (-1)) * (w b m hbm (1 : Rˣ))⁻¹ =
    w b L hbL v * w b L hbL (-1)
  rw [conj_mul_two, bruhatBigCell_w_first b m L hbm hbL hmL v,
    bruhatBigCell_w_first b m L hbm hbL hmL (-1)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_h_first

/-- A Weyl element inside `K × K` lies in `S`. -/
theorem bruhatBigCell_w_mem_S {K : Finset I} {i j : I} (hij : i ≠ j) (u : Rˣ) (hi : i ∈ K)
    (hj : j ∈ K) : w i j hij u ∈ bruhatBigCellS R K := by
  show x i j hij (u : R) * x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * x i j hij (u : R) ∈
    bruhatBigCellS R K
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (bruhatBigCell_x_mem_S hij _ hi hj)
    (bruhatBigCell_x_mem_S hij.symm _ hj hi)) (bruhatBigCell_x_mem_S hij _ hi hj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_w_mem_S

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
