import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2WeylSelf
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoRootSpan
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg symbols are central, over any commutative ring (k2-poly piece A5.1)

For a commutative ring `R`, indices `i ≠ j` and units `u, v`, the symbol is
`csym_ij(u, v) = h_ij(u v) h_ij(u)⁻¹ h_ij(v)⁻¹ ∈ St_I(R)`. This module proves that it is central
in `St_I(R)` once `I` has a third index.

In the van der Waerden argument over a field `F` (`K2Poly.FieldNagao`), Euclid's algorithm over
`F[X]` produces symbols of CONSTANT units, because the torus `c ↦ h_mL(c)` is no longer
multiplicative when `K₂(F) ≠ 1`. Centrality makes the target coset set `Z · S · V` a subgroup.

Method. Conjugation by `h_ij(u)` multiplies the coefficient of every root `x_kl` by `χ_kl(u)`, a
character `Rˣ →* Rˣ`: one of `u²`, `u⁻²`, `u`, `u⁻¹`, `1` (`hconj_exists`). The symbol therefore
acts by `χ(uv) χ(u)⁻¹ χ(v)⁻¹ = 1`. This is the commutative-ring form of bh-met-15's field
lemmas: `FieldK2.w_conj_x_self` and the `h_conj_*` family, restated with `↑(u⁻¹)` in place of
`(↑u)⁻¹`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_conj_x_row_i
  w_conj_x_row_j w_conj_x_col_i w_conj_x_col_j w_conj_x_disjoint x_congr)
open GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2 (conj_commutator')
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  rootSpan_induction mem_rootSpan_true)

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- A root element written as a commutator through a third index. -/
theorem cr_x_eq_commutator (i k j : I) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) (t : R) :
    x i j hij t = ⁅x i k hik t, x k j hkj 1⁆ := by
  rw [x_commutator i k j hik hkj hij t 1, mul_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.cr_x_eq_commutator

/-- `w_ij(u) x_ij(t) w_ij(u)⁻¹ = x_ji(-(u⁻¹ t u⁻¹))`. -/
theorem cr_w_conj_x_self (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (t : R) :
    w i j hij u * x i j hij t * (w i j hij u)⁻¹ =
      x j i hij.symm (-(((u⁻¹ : Rˣ) : R) * t * ((u⁻¹ : Rˣ) : R))) := by
  rw [cr_x_eq_commutator i k j hik hjk.symm hij t, conj_commutator',
    w_conj_x_row_i i j k hij hik hjk u t, w_conj_x_col_j i j k hij hik.symm hjk.symm u 1,
    x_commutator j k i hjk hik.symm hij.symm]
  exact x_congr _ _ rfl rfl (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.cr_w_conj_x_self

/-- `w_ij(u) x_ji(t) w_ij(u)⁻¹ = x_ij(-(u t u))`. -/
theorem cr_w_conj_x_self_symm (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (t : R) :
    w i j hij u * x j i hij.symm t * (w i j hij u)⁻¹ =
      x i j hij (-((u : R) * t * (u : R))) := by
  rw [cr_x_eq_commutator j k i hjk hik.symm hij.symm t, conj_commutator',
    w_conj_x_row_j i j k hij hik hjk u t, w_conj_x_col_i i j k hij hik.symm hjk.symm u 1,
    x_commutator i k j hik hjk.symm hij]
  exact x_congr _ _ rfl rfl (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.cr_w_conj_x_self_symm

/-- Conjugation by `h_ij(u)` is conjugation by `w_ij(-1)` followed by `w_ij(u)`. -/
theorem cr_h_conj_split (i j : I) (hij : i ≠ j) (u : Rˣ) (g : SteinbergGroup I R) :
    h i j hij u * g * (h i j hij u)⁻¹ =
      w i j hij u * (w i j hij (-1) * g * (w i j hij (-1))⁻¹) * (w i j hij u)⁻¹ := by
  simp only [h, mul_inv_rev, mul_assoc]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.cr_h_conj_split

/-- **Torus characters.**  For every root `(k, l)` there is a character `χ : Rˣ →* Rˣ` with
`h_ij(u) x_kl(t) h_ij(u)⁻¹ = x_kl(χ(u) t)`. -/
theorem hconj_exists (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hthird : ∃ n, i ≠ n ∧ j ≠ n) :
    ∃ χ : Rˣ →* Rˣ, ∀ (u : Rˣ) (t : R),
      h i j hij u * x k l hkl t * (h i j hij u)⁻¹ = x k l hkl ((χ u : R) * t) := by
  obtain ⟨n, hin, hjn⟩ := hthird
  by_cases hki : k = i
  · subst hki
    by_cases hlj : l = j
    · subst hlj
      refine ⟨powMonoidHom 2, fun u t => ?_⟩
      rw [cr_h_conj_split, cr_w_conj_x_self k l n hij hin hjn,
        cr_w_conj_x_self_symm k l n hij hin hjn]
      refine x_congr _ _ rfl rfl ?_
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, inv_neg_one, Units.val_neg,
        Units.val_one]
      ring
    · refine ⟨MonoidHom.id _, fun u t => ?_⟩
      rw [cr_h_conj_split, w_conj_x_row_i k j l hij hkl (Ne.symm hlj),
        w_conj_x_row_j k j l hij hkl (Ne.symm hlj)]
      refine x_congr _ _ rfl rfl ?_
      simp only [MonoidHom.id_apply, inv_neg_one, Units.val_neg, Units.val_one]
      ring
  · by_cases hkj : k = j
    · subst hkj
      by_cases hli : l = i
      · subst hli
        refine ⟨(powMonoidHom 2).comp (invMonoidHom : Rˣ →* Rˣ), fun u t => ?_⟩
        rw [cr_h_conj_split, cr_w_conj_x_self_symm l k n hij hin hjn,
          cr_w_conj_x_self l k n hij hin hjn]
        refine x_congr _ _ rfl rfl ?_
        simp only [MonoidHom.coe_comp, Function.comp_apply, invMonoidHom_apply, powMonoidHom_apply,
          Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
        ring
      · refine ⟨(invMonoidHom : Rˣ →* Rˣ), fun u t => ?_⟩
        rw [cr_h_conj_split, w_conj_x_row_j i k l hij (Ne.symm hli) hkl,
          w_conj_x_row_i i k l hij (Ne.symm hli) hkl]
        refine x_congr _ _ rfl rfl ?_
        simp only [invMonoidHom_apply, Units.val_neg, Units.val_one]
        ring
    · by_cases hli : l = i
      · subst hli
        refine ⟨(invMonoidHom : Rˣ →* Rˣ), fun u t => ?_⟩
        rw [cr_h_conj_split, w_conj_x_col_i l j k hij hkl hkj, w_conj_x_col_j l j k hij hkl hkj]
        refine x_congr _ _ rfl rfl ?_
        simp only [invMonoidHom_apply, Units.val_neg, Units.val_one]
        ring
      · by_cases hlj : l = j
        · subst hlj
          refine ⟨MonoidHom.id _, fun u t => ?_⟩
          rw [cr_h_conj_split, w_conj_x_col_j i l k hij hki hkl, w_conj_x_col_i i l k hij hki hkl]
          refine x_congr _ _ rfl rfl ?_
          simp only [MonoidHom.id_apply, inv_neg_one, Units.val_neg, Units.val_one]
          ring
        · refine ⟨1, fun u t => ?_⟩
          rw [cr_h_conj_split, w_conj_x_disjoint i j k l hij hkl (Ne.symm hki) (Ne.symm hkj)
            (Ne.symm hli) (Ne.symm hlj), w_conj_x_disjoint i j k l hij hkl (Ne.symm hki)
            (Ne.symm hkj) (Ne.symm hli) (Ne.symm hlj)]
          exact x_congr _ _ rfl rfl (by simp only [MonoidHom.one_apply, Units.val_one, one_mul])

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.hconj_exists

/-- The Steinberg symbol `h_ij(u v) h_ij(u)⁻¹ h_ij(v)⁻¹`, over a commutative ring. -/
def csym (i j : I) (hij : i ≠ j) (u v : Rˣ) : SteinbergGroup I R :=
  h i j hij (u * v) * (h i j hij u)⁻¹ * (h i j hij v)⁻¹

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.csym

/-- The inverse torus conjugation. -/
theorem hconj_inv {i j k l : I} {hij : i ≠ j} {hkl : k ≠ l} {χ : Rˣ →* Rˣ}
    (hχ : ∀ (u : Rˣ) (t : R),
      h i j hij u * x k l hkl t * (h i j hij u)⁻¹ = x k l hkl ((χ u : R) * t))
    (u : Rˣ) (s : R) :
    (h i j hij u)⁻¹ * x k l hkl s * h i j hij u = x k l hkl (((χ u)⁻¹ : Rˣ) * s) := by
  have e := hχ u ((((χ u)⁻¹ : Rˣ) : R) * s)
  rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at e
  rw [← e]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.hconj_inv

/-- **Symbols fix every root element.** -/
theorem csym_conj_x (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hthird : ∃ n, i ≠ n ∧ j ≠ n) (u v : Rˣ) (t : R) :
    csym i j hij u v * x k l hkl t * (csym i j hij u v)⁻¹ = x k l hkl t := by
  obtain ⟨χ, hχ⟩ := hconj_exists i j k l hij hkl hthird (R := R)
  have e : csym i j hij u v * x k l hkl t * (csym i j hij u v)⁻¹ =
      h i j hij (u * v) * ((h i j hij u)⁻¹ * ((h i j hij v)⁻¹ * x k l hkl t * h i j hij v) *
        h i j hij u) * (h i j hij (u * v))⁻¹ := by
    simp only [csym]
    group
  rw [e, hconj_inv hχ, hconj_inv hχ, hχ]
  refine x_congr _ _ rfl rfl ?_
  have hunit : χ (u * v) * (χ u)⁻¹ * (χ v)⁻¹ = 1 := by
    rw [map_mul, mul_comm (χ u) (χ v), mul_inv_cancel_right, mul_inv_cancel]
  rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul, hunit, Units.val_one, one_mul]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.csym_conj_x

/-- **Symbols are central** in `St_I(R)` (with a third index). -/
theorem csym_commute (i j : I) (hij : i ≠ j) (hthird : ∃ n, i ≠ n ∧ j ≠ n) (u v : Rˣ)
    (g : SteinbergGroup I R) : Commute (csym i j hij u v) g := by
  refine rootSpan_induction (p := fun _ _ => True)
    (Q := fun g => Commute (csym i j hij u v) g) ?_ (Commute.one_right _) ?_
    (mem_rootSpan_true g)
  · intro k l hkl t _
    have e := csym_conj_x i j k l hij hkl hthird u v t
    rw [mul_inv_eq_iff_eq_mul] at e
    exact e
  · intro a b _ _ ha hb
    exact ha.mul_right hb

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.csym_commute

end GroupApproximation.BooneHigmanLinear.K2Poly
