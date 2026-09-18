import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarNilCube
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilGeneric
import GroupApproximation.Meta.AxiomGuard

/-!
# The one-variable nil part over an arbitrary base ring, from the cube form

Lane `bh-met-44`, generic module.  Lane `bh-met-34` (module `ElemFPK2OneVarNilCube`) proved the
cube reduction `nil_of_cube` for an arbitrary commutative ring `R`: if every element of
`K₂(N, R[s_1..s_k])` killed by each substitution `s_i ↦ 0` dies after padding, then every element
killed by `ev₀` dies after padding.  Lane `bh-met-34` only used it over `F_p`.  This module uses it
over an arbitrary base ring `A`, to feed the one-variable half of the gap pair
`PolyK2NilGapStatementOver A d` of lane `bh-met-37`.

* `PolyK2CubeNilStatementOver A`: for `k ≥ 1`, `N ≥ k + 4`, `N ≥ 5`, an element of
  `K₂(N, A[s_1..s_k])` killed by each `s_i ↦ 0` dies after padding.
* `polyK2NilOver_of_cubeNil`: the cube form gives `PolyK2NilStatementOver A` (all `k`).  The case
  `k = 0` is `eq_one_of_K2Map_constantCoeff_eq_one`, and `k ≥ 1` is `nil_of_cube`.
* `polyK2OneVarNilOver_of_nil`: `PolyK2NilStatementOver A` gives `PolyK2OneVarNilStatementOver A`,
  through `A[s_0..s_k] ≅ A[s_1..s_k][s_0]` (`MvPolynomial.finSuccEquiv`).  For `N ≥ k + 5` the nil
  statement is applied at `k + 1` variables.
* `polyK2OneVarNilOver_of_cubeNil`: the composite.
* `polyK2CubeNilOver_of_nil`, `polyK2CubeNilOver_of_oneVar`: the converses, because
  `cc = cc ∘ π_0`.

Per instance `(k, N)`, the cube form has a stronger hypothesis than the nil statement at the same
`(k, N)` (killed by every `π_i`, not only by `cc`), so it asks for less.  The proof content
removed is the cube induction and the passage between one variable and `k + 1` variables.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Cube

variable (A : Type*) [CommRing A]

/-- **Cube form of the nil part over `A`.**  For `k ≥ 1`, `N ≥ k + 4`, `N ≥ 5`, an element of
`K₂(N, A[s_1..s_k])` killed by each substitution `s_i ↦ 0` dies after padding. -/
def PolyK2CubeNilStatementOver : Prop :=
  ∀ k N : ℕ, 0 < k → k + 4 ≤ N → 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) A),
      (∀ i : Fin k, K2Map (cubeKill A i) u = 1) →
        ∃ M : ℕ, ∃ hNM : N ≤ M,
          K2IndexMap (R := MvPolynomial (Fin k) A) (Fin.castLEEmb hNM) u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.PolyK2CubeNilStatementOver

end Cube

/-- The cube form gives the nil part for every number of variables. -/
theorem polyK2NilOver_of_cubeNil (A : Type*) [CommRing A] (h : PolyK2CubeNilStatementOver A) :
    PolyK2NilStatementOver A := by
  intro k N hkN h5N u hu
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨N, le_rfl, by rw [eq_one_of_K2Map_constantCoeff_eq_one hu, map_one]⟩
  · exact nil_of_cube (R := A) (k := k) (N := N) (fun v hv ↦ h k N hk hkN h5N v hv) u hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.polyK2NilOver_of_cubeNil

/-- The nil part at `k + 1` variables gives the one-variable nil part over `A[s_1..s_k]`. -/
theorem polyK2OneVarNilOver_of_nil (A : Type*) [CommRing A] (h : PolyK2NilStatementOver A) :
    PolyK2OneVarNilStatementOver A := by
  intro k N hkN u hu
  obtain ⟨M, hNM, hM⟩ := h (k + 1) N (by omega) (by omega)
    (K2Map (MvPolynomial.finSuccEquiv A k).toRingEquiv.symm.toRingHom u)
    (by
      rw [← constantCoeff_comp_finSuccEquiv (R := A) k, ← K2Map_K2Map, ← K2Map_K2Map,
        K2Map_K2Map_of_comp_eq_id _ _
          (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom_comp_symm_toRingHom,
        hu, map_one])
  refine ⟨M, hNM, ?_⟩
  rw [← K2Map_K2Map_of_comp_eq_id _ _
      (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom_comp_symm_toRingHom u,
    K2IndexMap_K2Map, hM, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.polyK2OneVarNilOver_of_nil

/-- **Generic endpoint**: the cube form gives the one-variable nil part over `A`. -/
theorem polyK2OneVarNilOver_of_cubeNil (A : Type*) [CommRing A]
    (h : PolyK2CubeNilStatementOver A) : PolyK2OneVarNilStatementOver A :=
  polyK2OneVarNilOver_of_nil A (polyK2NilOver_of_cubeNil A h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.polyK2OneVarNilOver_of_cubeNil

/-- Conversely, the nil part gives the cube form, because `cc = cc ∘ π_0`. -/
theorem polyK2CubeNilOver_of_nil (A : Type*) [CommRing A] (h : PolyK2NilStatementOver A) :
    PolyK2CubeNilStatementOver A := by
  intro k N hk hkN h5N u hu
  refine h k N hkN h5N u ?_
  rw [← constantCoeff_comp_cubeKill (R := A) (⟨0, hk⟩ : Fin k), ← K2Map_K2Map,
    hu ⟨0, hk⟩, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.polyK2CubeNilOver_of_nil

/-- Conversely, the one-variable nil part gives the cube form. -/
theorem polyK2CubeNilOver_of_oneVar (A : Type*) [CommRing A]
    (h : PolyK2OneVarNilStatementOver A) : PolyK2CubeNilStatementOver A :=
  polyK2CubeNilOver_of_nil A (polyK2NilOver_of_oneVar A h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.polyK2CubeNilOver_of_oneVar

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
