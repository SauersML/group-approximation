import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilLocal
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPZInvK2Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The cube gap over `ℤ[1/m]`, reduced to a local condition

Lane `bh-met-73c`.  The root hypothesis `hcube : CharZeroK2CubeGapPosStatement`
(module `ElemFPZInvK2Endpoint`) asks, for every `m ≥ 1` and `A = ℤ[1/m]`
(`Localization.Away (m : ℤ)`), for (i) the cube form `PolyK2CubeNilStatementOver A` and
(ii) diagonal injective stability `PolyK2StabRangeDiagStatementOver A 4`.

**LOUD: the other root hypotheses do not help.**  `hloc : PolyK2CubeNilLocalStatement` and
`hvdk : VdKRowExtensionStatement` are statements about the rings `F_p[s_1..s_k]` only.  There is
no ring map `F_p[s] → ℤ[1/m][s]`, and a map the other way cannot reflect triviality of `K₂`
elements, so no formal transfer exists.  What does transfer is the *proof* of the patching
reduction of `hloc` (module `ElemFPK2CubeNilLocal`), which is written for an arbitrary
commutative base ring (`diesAfterPadding_of_local`,
`evalZero_finSuccEquiv_comp_cubeKill_zero`).  This module redoes that reduction over `A`.

* `CZCubeGapLocalOverStatement A`: for `N ≥ k + 5`, `u ∈ K₂(N, A[s_0..s_k])` killed by every
  `π_i : s_i ↦ 0`, and a maximal ideal `𝔪` of `B = A[s_1..s_k]`, some `s ∉ 𝔪` makes
  `v_s(ψ u) = (ψ u)(t + s y) · (ψ u)(t)⁻¹` die after padding (`ψ = finSuccEquiv`, `s_0 ↦ t`).
* `czCubeGapCubeNilOver_of_local`: it gives `PolyK2CubeNilStatementOver A` (patching).
* `czCubeGapLocalOver_of_cubeNil`: the converse, with `s = 1`.
* `czCubeGapStabRangeDiagOver_of_rowParInjective`: over any `A`, injectivity of the parabolic
  map `vdkRowPar` at rank `k + 4` over `A[s_1..s_k]` gives `PolyK2StabRangeDiagStatementOver A 4`
  (van der Kallen's row-extension argument, module `ElemFPK2VdKRowEndpoint`, is ring-generic).
* `CZCubeGapLocalStatement`: for every `m ≥ 1`, the local form over `ℤ[1/m]` and the diagonal
  stability at offset `4`.  **This is the isolated gap.**
* `charZeroK2CubeGapPos_of_czCubeGapLocal`: **endpoint**, the gap gives `hcube`.
* `czCubeGapLocal_of_charZeroK2CubeGapPos`: the converse.

## Strength of the gap

**LOUD: the gap is logically equivalent to `CharZeroK2CubeGapPosStatement`** (both directions are
proved here).  No statement that implies the target *on its own* can be strictly weaker, and the
only other root inputs (`hloc`, `hvdk`) are about `F_p`, so strict logical weakening is not
available.  The gap is **strictly smaller in proof content** in half (i): the hypothesis is the
strongest available (killed by every `π_i`), the conclusion is local (one maximal ideal at a
time, one element of the Quillen ideal outside it), and the following are removed:
the ideal structure of the Quillen ideal and Krull's `Ideal.exists_le_maximal`, the collapse
`ρ σ_1 = id` turning `1 ∈ Q(w)` into the death of `w`, and the passage `A[s_0..s_k] ≅ B[t]` with
`ev_{t=0} ψ π_0 = ev_{t=0} ψ`.  Half (ii) is kept as it is: its row-injectivity form
(`czCubeGapStabRangeDiagOver_of_rowParInjective`) is smaller in content but logically
*stronger* (injectivity on all of `K₂(k + 4)`, not only on `ker ev₀`), so it is offered as a
proved reduction and not folded into the gap.

## Truth check

`m ≥ 1`, `A = ℤ[1/m]`, `S = A[s_1..s_k]`: regular noetherian of Krull dimension `k + 1`.

*(i)*  By the converse it suffices that the cube form holds.  An element killed by every `π_i`
is killed by `ev₀ = ev₀ ∘ π_0`.  Quillen: `NK₂` of the regular ring `A[s_1..s_{k}]` vanishes, so
the stable image is `0`, and stable `K₂` is the filtered colimit of `K₂(n, -)`, so the element
dies at a finite rank.  No rank bound is used.  **True.**  (Case `k = 0` of the local form:
`B = A`; the demand is met by `s = 1`, since the cube form gives death of `u` outright.)

*(ii)*  Bass: `sr(S) ≤ k + 2`.  Van der Kallen: `K₂(n, S) → K₂(n + 1, S)` is injective for
`n ≥ sr(S) + 2`; `n = k + 4` is covered (boundary case, as flagged in `ElemFPZInvK2Endpoint`;
Dennis's bound `n ≥ dim Max + 3 = k + 4` lands on the same rank).  **True.**  The same argument
makes the row-injectivity form true: `vdkRowPar (v, g)` has matrix `[[M_g, v], [0, 1]]`, so equal
images force `v = v'`, and then `stab g = stab g'`; `ker stab ≤ K₂`, so `g = g'`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Over

variable (A : Type*) [CommRing A]

/-- **Local form of the cube gap over `A`.**  For `N ≥ k + 5`, `u ∈ K₂(N, A[s_0..s_k])` killed by
every substitution `s_i ↦ 0`, and a maximal ideal `𝔪` of `B = A[s_1..s_k]`, some `s ∉ 𝔪` makes
`v_s(ψ u) = (ψ u)(t + s y) · (ψ u)(t)⁻¹ ∈ K₂(N, B[t][y])` die after padding, where
`ψ : A[s_0..s_k] ≅ B[t]` sends `s_0 ↦ t`. -/
def CZCubeGapLocalOverStatement : Prop :=
  ∀ k N : ℕ, k + 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin (k + 1)) A),
      (∀ i : Fin (k + 1), K2Map (cubeKill A i) u = 1) →
        ∀ m : Ideal (MvPolynomial (Fin k) A), m.IsMaximal →
          ∃ s : MvPolynomial (Fin k) A, s ∉ m ∧
            K2DiesAfterPadding
              (quillenDiff (K2Map (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom u) s)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CZCubeGapLocalOverStatement

/-- The local form gives the cube form over `A` (Quillen patching, `diesAfterPadding_of_local`). -/
theorem czCubeGapCubeNilOver_of_local (h : CZCubeGapLocalOverStatement A) :
    PolyK2CubeNilStatementOver A := by
  intro k N hk hkN _ u hu
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
  have hev : K2Map (Polynomial.evalRingHom 0 :
      Polynomial (MvPolynomial (Fin j) A) →+* MvPolynomial (Fin j) A)
        (K2Map (MvPolynomial.finSuccEquiv A j).toRingEquiv.toRingHom u) = 1 := by
    rw [K2Map_K2Map, ← evalZero_finSuccEquiv_comp_cubeKill_zero (R := A) j, ← K2Map_K2Map,
      hu 0, map_one]
  obtain ⟨M, hNM, hM⟩ := diesAfterPadding_of_local hev (h j N (by omega) u hu)
  refine ⟨M, hNM, ?_⟩
  rw [← K2Map_K2Map_of_comp_eq_id _ _
      (MvPolynomial.finSuccEquiv A j).toRingEquiv.symm_toRingHom_comp_toRingHom u,
    K2IndexMap_K2Map, hM, map_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeGapCubeNilOver_of_local

/-- Conversely, the cube form over `A` gives the local form, with `s = 1`. -/
theorem czCubeGapLocalOver_of_cubeNil (h : PolyK2CubeNilStatementOver A) :
    CZCubeGapLocalOverStatement A := by
  intro k N hkN u hu _ hm
  refine ⟨1, (Ideal.ne_top_iff_one _).mp hm.ne_top, ?_⟩
  exact diesAfterPadding_quillenDiff_of_diesAfterPadding
    (diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom
      (h (k + 1) N (Nat.succ_pos k) (by omega) (by omega) u hu)) 1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeGapLocalOver_of_cubeNil

/-- Over any `A`, injectivity of the parabolic map `vdkRowPar` at rank `k + 4` over
`A[s_1..s_k]` for every `k ≥ 1` gives diagonal injective stability at offset `4`. -/
theorem czCubeGapStabRangeDiagOver_of_rowParInjective
    (h : ∀ k : ℕ, 0 < k →
      Function.Injective (vdkRowPar (n := k + 4) (R := MvPolynomial (Fin k) A))) :
    PolyK2StabRangeDiagStatementOver A 4 :=
  fun k hk u _ hs ↦ K2Stab_eq_one_of_vdkRowPar_injective (h k hk) u hs

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeGapStabRangeDiagOver_of_rowParInjective

end Over

/-- **The isolated gap** (lane `bh-met-73c`): over every `ℤ[1/m]` with `m ≥ 1`, the local form of
the cube gap and diagonal injective stability on `ker ev₀` at rank `k + 4`.  LOUD: logically
equivalent to `CharZeroK2CubeGapPosStatement`, strictly smaller in proof content (see the module
docstring). -/
def CZCubeGapLocalStatement : Prop :=
  ∀ m : ℕ, 0 < m →
    CZCubeGapLocalOverStatement (Localization.Away (m : ℤ)) ∧
      PolyK2StabRangeDiagStatementOver (Localization.Away (m : ℤ)) 4

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CZCubeGapLocalStatement

/-- **Endpoint (lane `bh-met-73c`).**  The local gap gives the root hypothesis
`CharZeroK2CubeGapPosStatement`. -/
theorem charZeroK2CubeGapPos_of_czCubeGapLocal (h : CZCubeGapLocalStatement) :
    CharZeroK2CubeGapPosStatement :=
  fun m hm ↦ ⟨czCubeGapCubeNilOver_of_local _ (h m hm).1, (h m hm).2⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2CubeGapPos_of_czCubeGapLocal

/-- Conversely, `CharZeroK2CubeGapPosStatement` gives the local gap. -/
theorem czCubeGapLocal_of_charZeroK2CubeGapPos (h : CharZeroK2CubeGapPosStatement) :
    CZCubeGapLocalStatement :=
  fun m hm ↦ ⟨czCubeGapLocalOver_of_cubeNil _ (h m hm).1, (h m hm).2⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeGapLocal_of_charZeroK2CubeGapPos

/-- The local cube half over `ℤ[1/m]` and row injectivity at rank `k + 4` over
`ℤ[1/m][s_1..s_k]` give the root hypothesis.  (The row half is logically stronger than the
diagonal half; it is offered as an alternative input, not as the gap.) -/
theorem czCubeGap_charZeroK2CubeGapPos_of_local_of_rowPar
    (hloc : ∀ m : ℕ, 0 < m → CZCubeGapLocalOverStatement (Localization.Away (m : ℤ)))
    (hrow : ∀ m : ℕ, 0 < m → ∀ k : ℕ, 0 < k →
      Function.Injective
        (vdkRowPar (n := k + 4) (R := MvPolynomial (Fin k) (Localization.Away (m : ℤ))))) :
    CharZeroK2CubeGapPosStatement :=
  charZeroK2CubeGapPos_of_czCubeGapLocal fun m hm ↦
    ⟨hloc m hm, czCubeGapStabRangeDiagOver_of_rowParInjective _ (hrow m hm)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeGap_charZeroK2CubeGapPos_of_local_of_rowPar

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
