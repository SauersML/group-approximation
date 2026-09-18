import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellCells
import GroupApproximation.Meta.AxiomGuard

/-!
# Big Bruhat cell, part 6: proof of `BruhatBigCellStatement`

Lane `bh-met-64c`.

Proof route:

* Every `g ∈ G_{K ∪ {L}}` lies in `U P ∪ ⋃_j S w_jL P` (`bruhatBigCell_bru_of_mem`).
  This is `rootSpan_induction` on the property "left multiplication by `g` preserves the cells",
  using `bruhatBigCell_bru_S`, `bruhatBigCell_bru_U` and `bruhatBigCell_bru_V`, starting at
  `1 ∈ U P`.
* A small-cell element has `(g e_L)_L = 0` (`bruhatBigCell_small_act`):
  * `P` sends `e_L` to `c'⁻¹ e_L`, since `V` and `S` fix vectors that vanish on `K`;
  * `(w_jL(c) v)_L = -c⁻¹ v_j` (`bruhatBigCell_act_w_L`), and `v_j = 0`;
  * `S` does not touch coordinate `L`.
* So under `(g e_L)_L ≠ 0` the element is `u s v h_mL(c)`.  Over `ZMod p` the torus law
  `bruhatBigCell_h_mul_zmod` supplies `BruhatBigCellData` (`symbol_eq_one_zmod`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act unitVec
  act_mul act_x_apply rootSpan_induction act_apply_of_rootSpan act_eq_self_of_rootSpan)

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- `(w_jL(c) v)_L = -c⁻¹ v_j`. -/
theorem bruhatBigCell_act_w_L (j L : I) (hjL : j ≠ L) (c : Rˣ) (v : I → R) :
    act (w j L hjL c) v L = -(((c⁻¹ : Rˣ) : R) * v j) := by
  rw [w, act_mul, act_mul, act_x_apply, if_neg hjL.symm, add_zero, act_x_apply, if_pos rfl,
    act_x_apply, act_x_apply, if_neg hjL.symm, add_zero, if_pos rfl]
  linear_combination (-(v L)) * Units.inv_mul c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_act_w_L

/-- A small-cell element kills the `(L, L)` entry. -/
theorem bruhatBigCell_small_act (σ : BruhatBigCellData I R) {g : SteinbergGroup I R}
    (hg : bruhatBigCellSmall σ g) : act g (unitVec σ.L) σ.L = 0 := by
  obtain ⟨j, hj, c, s, hs, q, hq, rfl⟩ := hg
  obtain ⟨s', hs', v, hv, c', rfl⟩ := (bruhatBigCell_mem_par σ).mp hq
  have hw₀ : ∀ k ∈ σ.K, act (h σ.m σ.L σ.hmL c') (unitVec σ.L) k = 0 := by
    intro k hk
    rw [bruhat_act_h_unitVec, if_neg (bruhatBigCell_ne σ.hLK hk)]
  have hqe : act (s' * v * h σ.m σ.L σ.hmL c') (unitVec σ.L) =
      act (h σ.m σ.L σ.hmL c') (unitVec σ.L) := by
    rw [act_mul, act_mul,
      act_eq_self_of_rootSpan (p := fun i l => i = σ.L ∧ l ∈ σ.K)
        (w := act (h σ.m σ.L σ.hmL c') (unitVec σ.L)) (fun _ l hp => hw₀ l hp.2) hv,
      act_eq_self_of_rootSpan (p := fun i l => i ∈ σ.K ∧ l ∈ σ.K)
        (w := act (h σ.m σ.L σ.hmL c') (unitVec σ.L)) (fun _ l hp => hw₀ l hp.2) hs']
  rw [act_mul, act_mul,
    act_apply_of_rootSpan (p := fun i l => i ∈ σ.K ∧ l ∈ σ.K)
      (fun i _ hp => bruhatBigCell_ne σ.hLK hp.1) hs,
    hqe, bruhatBigCell_act_w_L, hw₀ j hj, mul_zero, neg_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_small_act

/-- Every element of `G_{K ∪ {L}}` lies in one of the cells. -/
theorem bruhatBigCell_bru_of_mem (σ : BruhatBigCellData I R) {g : SteinbergGroup I R}
    (hg : g ∈ rootSpan (R := R) (fun i j => i ∈ insert σ.L σ.K ∧ j ∈ insert σ.L σ.K)) :
    bruhatBigCellBru σ g := by
  have hone : bruhatBigCellBru σ 1 :=
    Or.inl ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by rw [one_mul]⟩
  have H : ∀ z, bruhatBigCellBru σ z → bruhatBigCellBru σ (g * z) := by
    refine rootSpan_induction (p := fun i j => i ∈ insert σ.L σ.K ∧ j ∈ insert σ.L σ.K)
      (Q := fun g => ∀ z, bruhatBigCellBru σ z → bruhatBigCellBru σ (g * z)) ?_ ?_ ?_ hg
    · intro i j hij a hp z hz
      obtain ⟨hi, hj⟩ := hp
      rcases Finset.mem_insert.mp hi with hiL | hiK
      · subst i
        rcases Finset.mem_insert.mp hj with hjL | hjK
        · exact absurd hjL.symm hij
        · exact bruhatBigCell_bru_V σ hjK a hz
      · rcases Finset.mem_insert.mp hj with hjL | hjK
        · subst j
          exact bruhatBigCell_bru_U σ (bruhatBigCell_x_mem_U hij a hiK) hz
        · exact bruhatBigCell_bru_S σ (bruhatBigCell_x_mem_S hij a hiK hjK) hz
    · intro z hz
      rw [one_mul]
      exact hz
    · intro g₁ g₂ _ _ h₁ h₂ z hz
      rw [mul_assoc]
      exact h₁ _ (h₂ z hz)
  have h1 := H 1 hone
  rw [mul_one] at h1
  exact h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_bru_of_mem

/-- The big-cell factorization over any field whose torus `h_mL` is multiplicative. -/
theorem bruhatBigCell_of_data (σ : BruhatBigCellData I R) {g : SteinbergGroup I R}
    (hg : g ∈ rootSpan (R := R) (fun i j => i ∈ insert σ.L σ.K ∧ j ∈ insert σ.L σ.K))
    (hact : act g (unitVec σ.L) σ.L ≠ 0) :
    ∃ u ∈ rootSpan (R := R) (fun i j => j = σ.L ∧ i ∈ σ.K),
      ∃ s ∈ rootSpan (R := R) (fun i j => i ∈ σ.K ∧ j ∈ σ.K),
        ∃ v ∈ rootSpan (R := R) (fun i j => i = σ.L ∧ j ∈ σ.K),
          ∃ c : Rˣ, g = u * s * v * h σ.m σ.L σ.hmL c := by
  rcases bruhatBigCell_bru_of_mem σ hg with ⟨u, hu, q, hq, rfl⟩ | hsmall
  · obtain ⟨s, hs, v, hv, c, rfl⟩ := (bruhatBigCell_mem_par σ).mp hq
    exact ⟨u, hu, s, hs, v, hv, c, by group⟩
  · exact absurd (bruhatBigCell_small_act σ hsmall) hact

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_of_data

/-- **The big Bruhat cell over `F_p`**: `BruhatBigCellStatement` holds. -/
theorem bruhatBigCell : BruhatBigCellStatement := by
  intro p _ I _ _ hI K L m hLK hmK hmL g hg hact
  obtain ⟨k, hmk, hLk⟩ := bruhatBigCell_third hI m L
  exact bruhatBigCell_of_data ⟨K, L, m, hmL, hLK, hmK, bruhatBigCell_third hI,
    bruhatBigCell_h_mul_zmod m L k hmL hmk hLk⟩ hg hact

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
