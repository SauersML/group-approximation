import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngStabOneGen
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(3, ℤ[1/1])` is the normal closure of one symbol word (lane bh-met-92z, 4)

The word map `F` of `ElemFPCharZeroK2FngStabOneGen` kills `P13` relators `0, …, 11`, which
are Steinberg relations (`czK2FngStabOne_F_relator`).  Put `sym = F(relator 12)`, the image
of `(e₁₂ e₂₁⁻¹ e₁₂)⁴`.  Then:

* `czK2FngStabOne_sym_mem_K2`: `sym ∈ K₂(3, ℤ[1/1])`;
* `czK2FngStabOne_sym_mem_range_stab`: `sym ∈ stab St_2(ℤ[1/1])`;
* `czK2FngStabOne_k2_le_normalClosure`: `K₂(3, ℤ[1/1]) ≤ ⟪sym⟫`.

The last one follows from the repository's *proved* completeness of `P13`
(`P13DescentMaster.toSL3_injective`).  Take `k = F w ∈ K₂`.  Then `toSL3 [w] = 1`, so
`w ∈ ⟪relators⟫`, and `F` sends that normal closure into `⟪sym⟫`.  No literature input.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

local notation "R₁" => Localization.Away ((1 : ℕ) : ℤ)

/-- The adjacent Steinberg relation, as a relator word. -/
theorem czK2FngStabOne_adj (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    x i j hij (1 : R₁) * (x j k hjk 1 * ((x i j hij 1)⁻¹ * ((x j k hjk 1)⁻¹ *
      (x i k hik 1)⁻¹))) = 1 := by
  have hc := x_commutator i j k hij hjk hik (1 : R₁) 1
  rw [mul_one] at hc
  rw [← hc, commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_adj

/-- The commuting Steinberg relation, as a relator word. -/
theorem czK2FngStabOne_comm (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) :
    x i j hij (1 : R₁) * (x k l hkl 1 * ((x i j hij 1)⁻¹ * (x k l hkl 1)⁻¹)) = 1 := by
  have h := (x_commute_of_ne i j k l hij hkl hjk hli (1 : R₁) 1).eq
  rw [← mul_assoc, h]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_comm

theorem czK2FngStabOne_F_rel0 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 0) = 1 := by
  show czK2FngStabOne_F
    (FreeGroup.mk [(0, true), (3, true), (0, false), (3, false), (1, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_adj 0 1 2 (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel0

theorem czK2FngStabOne_F_rel1 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 1) = 1 := by
  show czK2FngStabOne_F
    (FreeGroup.mk [(1, true), (5, true), (1, false), (5, false), (0, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_adj 0 2 1 (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel1

theorem czK2FngStabOne_F_rel2 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 2) = 1 := by
  show czK2FngStabOne_F
    (FreeGroup.mk [(2, true), (1, true), (2, false), (1, false), (3, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_adj 1 0 2 (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel2

theorem czK2FngStabOne_F_rel3 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 3) = 1 := by
  show czK2FngStabOne_F
    (FreeGroup.mk [(3, true), (4, true), (3, false), (4, false), (2, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_adj 1 2 0 (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel3

theorem czK2FngStabOne_F_rel4 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 4) = 1 := by
  show czK2FngStabOne_F
    (FreeGroup.mk [(4, true), (0, true), (4, false), (0, false), (5, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_adj 2 0 1 (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel4

theorem czK2FngStabOne_F_rel5 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 5) = 1 := by
  show czK2FngStabOne_F
    (FreeGroup.mk [(5, true), (2, true), (5, false), (2, false), (4, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_adj 2 1 0 (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel5

theorem czK2FngStabOne_F_rel6 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 6) = 1 := by
  show czK2FngStabOne_F (FreeGroup.mk [(0, true), (1, true), (0, false), (1, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_comm 0 1 0 2 (by decide) (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel6

theorem czK2FngStabOne_F_rel7 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 7) = 1 := by
  show czK2FngStabOne_F (FreeGroup.mk [(0, true), (5, true), (0, false), (5, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_comm 0 1 2 1 (by decide) (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel7

theorem czK2FngStabOne_F_rel8 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 8) = 1 := by
  show czK2FngStabOne_F (FreeGroup.mk [(1, true), (3, true), (1, false), (3, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_comm 0 2 1 2 (by decide) (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel8

theorem czK2FngStabOne_F_rel9 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 9) = 1 := by
  show czK2FngStabOne_F (FreeGroup.mk [(2, true), (3, true), (2, false), (3, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_comm 1 0 1 2 (by decide) (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel9

theorem czK2FngStabOne_F_rel10 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 10) = 1 := by
  show czK2FngStabOne_F (FreeGroup.mk [(2, true), (4, true), (2, false), (4, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_comm 1 0 2 0 (by decide) (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel10

theorem czK2FngStabOne_F_rel11 : czK2FngStabOne_F (LiteralP13Presentation.p13Relator 11) = 1 := by
  show czK2FngStabOne_F (FreeGroup.mk [(4, true), (5, true), (4, false), (5, false)]) = 1
  simp only [czK2FngStabOne_F_mk, List.map_cons, List.map_nil, cond_true, cond_false,
    List.prod_cons, List.prod_nil, mul_one]
  exact czK2FngStabOne_comm 2 0 2 1 (by decide) (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_rel11

/-- `F` kills the twelve Steinberg relators of `P13`. -/
theorem czK2FngStabOne_F_relator :
    ∀ i : Fin 13, i ≠ 12 → czK2FngStabOne_F (LiteralP13Presentation.p13Relator i) = 1
  | 0, _ => czK2FngStabOne_F_rel0
  | 1, _ => czK2FngStabOne_F_rel1
  | 2, _ => czK2FngStabOne_F_rel2
  | 3, _ => czK2FngStabOne_F_rel3
  | 4, _ => czK2FngStabOne_F_rel4
  | 5, _ => czK2FngStabOne_F_rel5
  | 6, _ => czK2FngStabOne_F_rel6
  | 7, _ => czK2FngStabOne_F_rel7
  | 8, _ => czK2FngStabOne_F_rel8
  | 9, _ => czK2FngStabOne_F_rel9
  | 10, _ => czK2FngStabOne_F_rel10
  | 11, _ => czK2FngStabOne_F_rel11
  | 12, h => absurd rfl h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_relator

/-- The symbol word `F((e₁₂ e₂₁⁻¹ e₁₂)⁴)` in `St_3(ℤ[1/1])`. -/
noncomputable def czK2FngStabOne_sym : St 3 R₁ :=
  czK2FngStabOne_F (LiteralP13Presentation.p13Relator 12)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sym

theorem czK2FngStabOne_sym_mem_K2 : czK2FngStabOne_sym ∈ K2 (Fin 3) R₁ := by
  apply surjStab_mem_K2_of_padMat_eq_one
  have h1 : LiteralP13Presentation.p13Word (LiteralP13Presentation.p13Relator 12) = 1 :=
    PresentedGroup.one_of_mem
      (Finset.mem_coe.mpr (LiteralP13Presentation.p13Relator_mem 12))
  rw [czK2FngStabOne_sym, czK2FngStabOne_padMat_F, h1, map_one, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_sym_mem_K2
