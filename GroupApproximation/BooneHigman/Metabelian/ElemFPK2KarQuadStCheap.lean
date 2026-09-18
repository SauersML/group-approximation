import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarQuadRelStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Four relative conjugates: the stably datum-cheap case (Hurwitz orbit of rank-one pairs)

Lane `bh-met-93w`, core module.  `P = k2DilateSt_pullback s`, `A` a domain, `s ≠ 0`.

* `k2KarQuadSt_DatumCheap y`: some padding of `y`, conjugated by some `c`, equals
  `Y · (g₃ x_kl(c₃) g₃⁻¹) · (g₄ x_ij(c₄) g₄⁻¹)` with `(Y, V, W)` a rank-one datum
  (`stab Y = ⁅padCol V, padRow W⁆`, `padMat Y = 1 + V Wᵀ`, `W ⬝ᵥ V = 0`).
* **`k2KarQuadSt_stDies_of_datumCheap`**: a datum-cheap `y` with `St(snd) y = 1` dies after
  padding (`k2KarQuad_stDies_datum_mul_two`, conjugation and padding invariance of death).
* **`k2KarQuadSt_datumCheap_of_factor`**: if a padded conjugate of `y` is `w₁ w₂ w₃ w₄` with all
  `wᵢ` relative conjugates and `PairRankOne (w₁ w₂)`, then `y` is datum-cheap
  (`k2KarTri_rankOneAt_two` upgrades `w₁ w₂` to a rank-one datum).
* **Pair lemmas** `k2KarQuadSt_datumCheap_of_pair12/23/13/24`: `z₁ z₂ z₃ z₄` is datum-cheap as
  soon as ONE of `z₁ z₂`, `z₂ z₃`, `z₁ z₃`, `z₂ z₄` is `PairRankOne`.  The pairs `(1,3)` and
  `(2,4)` are NEW (only `(1,2)`, `(2,3)` were handled in `bh-met-93q`); they come from the
  Steinberg-level Hurwitz moves
  `z₁ z₂ z₃ z₄ = b · z₁ z₃ z₄`, `b = z₁ z₂ z₁⁻¹`, and
  `z₁ z₂ z₃ z₄ = z₁ c' · z₂ z₄`, `c' = z₂ z₃ z₂⁻¹`, followed by rotation
  (free-group identities, checked in `bh-met-93w/truth_check.py`).

Truth check (`bh-met-93w/truth_check.py`, over `ℤ[T]`): there are relative tuples with product
`1`, both adjacent pairs of rank `2` (so outside `bh-met-93q`), but `z₁ z₃ = 1 + V Wᵀ`,
`W ⬝ᵥ V = 0`; so the new class meets the domain of `k2KarQuad_GenericAt`.

Relativity is used only for the shape `g x_ij(b) g⁻¹`; `snd` only via `padMat`
(`k2KarInd_padMat_eq_one`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarQuadStCheapDef

/-- **Stably datum-cheap**: a padded conjugate of `y` is a rank-one datum times two
conjugated root elements. -/
def k2KarQuadSt_DatumCheap {A : Type*} [CommRing A] {s : A} {M : ℕ}
    (y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)) : Prop :=
  ∃ (M' : ℕ) (hM : M ≤ M') (c Y g₃ g₄ : St M' (k2DilateSt_pullback s))
    (V W : Fin M' → k2DilateSt_pullback s) (k l : Fin M') (hkl : k ≠ l)
    (c₃ : k2DilateSt_pullback s) (i j : Fin M') (hij : i ≠ j) (c₄ : k2DilateSt_pullback s),
    stab M' (k2DilateSt_pullback s) Y = ⁅padCol V, padRow W⁆ ∧
      padMat Y = 1 + Matrix.vecMulVec V W ∧ W ⬝ᵥ V = 0 ∧
        c * SteinbergGroup.indexMap (Fin.castLEEmb hM) y * c⁻¹ =
          Y * (g₃ * x k l hkl c₃ * g₃⁻¹) * (g₄ * x i j hij c₄ * g₄⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_DatumCheap

/-- Padding along `le_refl` is the identity. -/
theorem k2KarQuadSt_indexMap_refl {R : Type*} [Ring R] {M : ℕ}
    (y : SteinbergGroup (Fin M) R) :
    SteinbergGroup.indexMap (Fin.castLEEmb (le_refl M)) y = y := by
  have hh : SteinbergGroup.indexMap (R := R) (Fin.castLEEmb (le_refl M)) = MonoidHom.id _ := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change SteinbergGroup.indexMap (Fin.castLEEmb (le_refl M)) (x i j hij a) = x i j hij a
    rw [SteinbergGroup.indexMap_x]
    rfl
  exact DFunLike.congr_fun hh y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_indexMap_refl

end KarQuadStCheapDef
