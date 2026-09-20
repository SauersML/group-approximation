import GroupApproximation.BooneHigmanLinear.LSCore.SMapCore
import GroupApproximation.BooneHigmanLinear.LSCore.Symbols
import Mathlib.Algebra.Ring.Hom.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# The map `S_α(a, -)` in `St_I(R)` and Lavrenov–Sinchuk Lemma 5.28 (k2-poly H.L4)

A. Lavrenov, S. Sinchuk, *A Horrocks-type theorem for even orthogonal K₂*, Doc. Math. 25
(2020), arXiv:1909.02637, §5.3. Lane k2-hl4c.

Take a ring map `φ : A → R` (L–S: `A → A[X, X⁻¹]`), a unit `t` of `R` (L–S: `X`) and a root
`α = (i, j)`. `sData hF φ t` is the data of L–S Def 5.26 for `LSCore/SMapCore.lean`:
* `y c = x_α(φ(c) t⁻¹)`, i.e. `x_α(c X⁻¹)`;
* `sym u = {t, φ(u)}_α` for units `u`, i.e. `{X, u}`; its multiplicativity and centrality come from
  the named bundle `SymbolFacts` of `LSCore/Symbols.lean`.

`sMapAt_xn` is **L–S Lemma 5.28**:
`S_α(a, x_{-α}(mX)) = x_{-α}(mX/(1+am)) · ⟨a, m⟩_α · h_α(1+am)`.
The proof is L–S's: expand `x_α(aX⁻¹) x_{-α}(mX)` by (2.14) and apply (5.12) (`dsym_scale_mul`).
Lemma 5.27 is `SMapCore.SData.sMapAt_mul` for this data. Cor 5.29 and Lemma 5.30 follow from
`SMapCore.sMapAt_inCoset` and `SMapCore.sMapAt_pair_inCoset` once `P_α(0)` (`LSCore/PDef.lean`),
Lemma 5.24 and the membership of `⟨a, m⟩_α` in `P_α(0)` (L–S 5.11) are supplied.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h x_congr)

variable {I R A : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing A]

open scoped Classical in
/-- The data of L–S Def 5.26 in `St_I(R)`: `y c = x_α(φ(c) t⁻¹)` and `sym u = {t, φ(u)}_α`. -/
noncomputable def sData {i j : I} {hij : i ≠ j} (hF : SymbolFacts R i j hij) (φ : A →+* R)
    (t : Rˣ) : SMapCore.SData (SteinbergGroup I R) A where
  y c := x i j hij (φ c * ((t⁻¹ : Rˣ) : R))
  y_add b c := by
    show x i j hij (φ (b + c) * ((t⁻¹ : Rˣ) : R)) =
      x i j hij (φ b * ((t⁻¹ : Rˣ) : R)) * x i j hij (φ c * ((t⁻¹ : Rˣ) : R))
    rw [x_mul, map_add, add_mul]
  sym u := if hu : IsUnit u then ssym i j hij t (Units.map (φ : A →* R) hu.unit) else 1
  sym_mul u v hu hv := by
    simp only [dif_pos hu, dif_pos hv, dif_pos (hu.mul hv)]
    rw [IsUnit.unit_mul, map_mul]
    exact hF.ssym_mul_right _ _ _
  sym_central u g hu := by
    simp only [dif_pos hu]
    exact hF.ssym_central _ _ g

/-- **L–S Lemma 5.28**: `S_α(a, x_{-α}(mX)) = x_{-α}(mX/(1+am)) · ⟨a, m⟩_α · h_α(1+am)`, with
`γ = (j, l)` the auxiliary root of L–S (5.12). -/
theorem sMapAt_xn {i j l : I} {hij : i ≠ j} (hF : SymbolFacts R i j hij) (hjl : j ≠ l)
    (hil : i ≠ l) (φ : A →+* R) (t : Rˣ) (a m : A) (hw : IsUnit (1 + a * m)) :
    (sData hF φ t).sMapAt a m (x j i hij.symm (φ m * (t : R))) =
      x j i hij.symm (φ (m * Ring.inverse (1 + a * m)) * (t : R)) *
        dsym i j hij (φ a) (φ m) (Units.map (φ : A →* R) hw.unit) *
        h i j hij (Units.map (φ : A →* R) hw.unit) := by
  simp only [SMapCore.SData.sMapAt, sData, dif_pos hw]
  generalize hU0 : Units.map (φ : A →* R) hw.unit = U
  have hU : (U : R) = 1 + φ a * φ m := by
    rw [← hU0]
    show φ (1 + a * m) = _
    rw [map_add, map_one, map_mul]
  have hinv : φ (Ring.inverse (1 + a * m)) = ((U⁻¹ : Rˣ) : R) := by
    rw [← hU0, Ring.inverse_of_isUnit hw]
    rfl
  have hcancel : x i j hij (φ a * ((t⁻¹ : Rˣ) : R) * ((U⁻¹ : Rˣ) : R)) *
      x i j hij (φ (-(a * Ring.inverse (1 + a * m))) * ((t⁻¹ : Rˣ) : R)) = 1 := by
    rw [x_mul, map_neg, map_mul, hinv,
      show φ a * ((t⁻¹ : Rˣ) : R) * ((U⁻¹ : Rˣ) : R) +
        -(φ a * ((U⁻¹ : Rˣ) : R)) * ((t⁻¹ : Rˣ) : R) = 0 by ring, x_zero]
  have hcomm : h i j hij U * ssym i j hij t U = ssym i j hij t U * h i j hij U :=
    ((hF.ssym_central t U (h i j hij U)).eq).symm
  have hxn : x j i hij.symm (φ m * (t : R) * ((U⁻¹ : Rˣ) : R)) =
      x j i hij.symm (φ (m * Ring.inverse (1 + a * m)) * (t : R)) := by
    rw [map_mul, hinv]
    exact x_congr _ _ rfl rfl (by ring)
  have e : ∀ P Q H Y Z S : SteinbergGroup I R, Y * Z = 1 → H * S = S * H →
      P * Q * H * Y * Z * S = P * (Q * S) * H := by
    intro P Q H Y Z S hYZ hHS
    calc P * Q * H * Y * Z * S = P * Q * H * (Y * Z) * S := by group
      _ = P * Q * (H * S) := by rw [hYZ]; group
      _ = P * (Q * S) * H := by rw [hHS]; group
  rw [x_mul_x_dsym i j hij (φ a * ((t⁻¹ : Rˣ) : R)) (φ m * (t : R)) U,
    e _ _ _ _ _ _ hcancel hcomm, dsym_scale_mul hF hjl hil t U (φ a) (φ m) hU, hxn]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.sMapAt_xn

end LSCore
end BooneHigmanLinear
end GroupApproximation
