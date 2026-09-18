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
