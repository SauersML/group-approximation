import GroupApproximation.BooneHigman.Metabelian.ElemFPK2LocalQuillenIdeal
import GroupApproximation.Meta.AxiomGuard

/-!
# The cube gap for the nil part of `K₂(N, F_p[s_0..s_k])`, reduced to a local condition

Lane `bh-met-46b` (re-dispatch of lane `bh-met-46`, "NK₂ core").  Lane `bh-met-34` isolated
`PolyK2CubeNilStatement` (module `ElemFPK2OneVarNilCube`): for `k ≥ 1`, `N ≥ k + 4`, `N ≥ 5`, an
element of `K₂(N, F_p[s_0..s_{k-1}])` killed by every substitution `s_i ↦ 0` dies after padding.
Lane `bh-met-46` proved the patching half of Quillen's local-global principle
(module `ElemFPK2LocalQuillenIdeal`, `diesAfterPadding_of_local`) but did not wire it.  This module
wires it into the cube gap.

Write `B = F_p[s_1..s_k]`, `ψ = MvPolynomial.finSuccEquiv : F_p[s_0..s_k] ≅ B[t]` (`s_0 ↦ t`),
`π_i = cubeKill` and, for `w ∈ K₂(N, B[t])`, `v_a(w) = w(t + a y) · w(t)⁻¹ = quillenDiff w a`.

* `evalZero_finSuccEquiv_comp_cubeKill_zero`: `ev_{t=0} ∘ ψ ∘ π_0 = ev_{t=0} ∘ ψ`, checked on the
  constants and on the variables.
* `PolyK2CubeNilLocalStatement`: for `N ≥ k + 5`, `u ∈ K₂(N, F_p[s_0..s_k])` killed by every
  `π_i`, and a maximal ideal `m` of `B`, some `s ∉ m` makes `v_s(ψ u)` die after padding.
  **This is the isolated gap.**
* `polyK2CubeNil_of_cubeLocal`: the local gap gives the cube gap.  Put `k = j + 1`.  Since
  `π_0 u = 1`, `ev_{t=0}(ψ u) = ev_{t=0} ψ π_0 u = 1`.  Patching (`diesAfterPadding_of_local`)
  makes `ψ u` die after padding, and `ψ⁻¹` carries this back to `u` (`K2IndexMap_K2Map`).
* `polyK2CubeNilLocal_of_cubeNil`: the converse, with `s = 1 ∉ m`: if `u` dies then so do `ψ u`
  and `v_1(ψ u)` (`diesAfterPadding_quillenDiff_of_diesAfterPadding`).
* `polyK2NilPos_of_cubeLocal`, `polyK2OneVarNil_of_cubeLocal`: the gap wired to lane `bh-met-14`'s
  `PolyK2NilPosStatement` and to the frontier item `PolyK2OneVarNilStatement`.

## Why the target is not closed here

The cube gap is `NK₂(F_p[s_1..s_k]) = 0` in unstable form.  Its proof is Quillen's homotopy
invariance for regular rings (through the localization sequence and dévissage), far beyond what
the repository has.  Even the next local step, the dilation lemma "if `w` dies over `B_s[t]` then
`v_{s^r}(w)` dies over `B[t][y]` for large `r`" (Tulenbaev), is a long Steinberg-group word
calculation.

## Why the gap is strictly smaller in proof content

**LOUD: the two statements are logically equivalent**, and both directions are proved here.  The
gap asks less *per instance*: the hypothesis on `u` is the strongest one available (killed by every
`π_i`, not only by `ev₀`), and the conclusion is local: one maximal ideal at a time, one element
of the Quillen ideal `Q(ψ u)` outside it.  The proof content removed is

* the ideal structure of `Q(w)` (closure under addition through `τ_b σ_a = σ_{a+b}`, under
  multiplication through `μ_c σ_a = σ_{c a}`) and Krull's `Ideal.exists_le_maximal`;
* the collapse `ρ σ_1 = id`, `ρ C = C ∘ ev_{t=0}`, turning `1 ∈ Q(w)` into the death of `w`;
* the passage `F_p[s_0..s_k] ≅ B[t]` and `ev_{t=0} ψ π_0 = ev_{t=0} ψ`;
* downstream, the cube induction `nil_of_cube` and the one-variable induction (lanes `bh-met-34`,
  `bh-met-22`).

## Truth check

By the converse the gap follows from `PolyK2CubeNilStatement`.  That statement is true: an element
killed by every `π_i` is killed by `ev₀ = ev₀ ∘ π_0`.  `F_p[s_0..s_k]` is regular noetherian, so by
Quillen `NK₂` vanishes and the stable image of `u` is `0`.  Stable `K₂ = ker(St → E)` is the
filtered colimit of the unstable `K₂(n, -)`, so `u` dies at some finite rank.  No rank bound is
used, so `N ≥ k + 5` is harmless.  For `k = 0`, `B = F_p` is a field, its only maximal ideal is
`⊥`, and the demand is that some nonzero `s` has `v_s(ψ u)` dying, which `s = 1` meets.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- `ev_{t=0} ∘ ψ ∘ π_0 = ev_{t=0} ∘ ψ`, where `ψ : R[s_0..s_k] ≅ R[s_1..s_k][t]` sends `s_0 ↦ t`. -/
theorem evalZero_finSuccEquiv_comp_cubeKill_zero {R : Type*} [CommRing R] (k : ℕ) :
    ((Polynomial.evalRingHom 0 :
          Polynomial (MvPolynomial (Fin k) R) →+* MvPolynomial (Fin k) R).comp
        (MvPolynomial.finSuccEquiv R k).toRingEquiv.toRingHom).comp
          (cubeKill R (0 : Fin (k + 1))) =
      (Polynomial.evalRingHom 0 :
          Polynomial (MvPolynomial (Fin k) R) →+* MvPolynomial (Fin k) R).comp
        (MvPolynomial.finSuccEquiv R k).toRingEquiv.toRingHom :=
  MvPolynomial.ringHom_ext
    (fun r ↦ by
      show Polynomial.eval 0 (MvPolynomial.finSuccEquiv R k
          (cubeKill R (0 : Fin (k + 1)) (MvPolynomial.C r : MvPolynomial (Fin (k + 1)) R))) =
        Polynomial.eval 0 (MvPolynomial.finSuccEquiv R k
          (MvPolynomial.C r : MvPolynomial (Fin (k + 1)) R))
      rw [cubeKill_C])
    fun l ↦ by
      by_cases hl : l = 0
      · subst hl
        show Polynomial.eval 0 (MvPolynomial.finSuccEquiv R k
            (cubeKill R (0 : Fin (k + 1)) (MvPolynomial.X 0 : MvPolynomial (Fin (k + 1)) R))) =
          Polynomial.eval 0 (MvPolynomial.finSuccEquiv R k
            (MvPolynomial.X 0 : MvPolynomial (Fin (k + 1)) R))
        rw [cubeKill_X_of_eq (R := R) rfl, map_zero, MvPolynomial.finSuccEquiv_X_zero,
          Polynomial.eval_zero, Polynomial.eval_X]
      · show Polynomial.eval 0 (MvPolynomial.finSuccEquiv R k
            (cubeKill R (0 : Fin (k + 1)) (MvPolynomial.X l : MvPolynomial (Fin (k + 1)) R))) =
          Polynomial.eval 0 (MvPolynomial.finSuccEquiv R k
            (MvPolynomial.X l : MvPolynomial (Fin (k + 1)) R))
        rw [cubeKill_X_of_ne hl]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.evalZero_finSuccEquiv_comp_cubeKill_zero

/-- **The isolated gap**: the local form of the cube gap.  For `N ≥ k + 5`, an element
`u ∈ K₂(N, F_p[s_0..s_k])` killed by every substitution `s_i ↦ 0`, and a maximal ideal `m` of
`B = F_p[s_1..s_k]`, some `s ∉ m` makes `v_s(ψ u) = (ψ u)(t + s y) · (ψ u)(t)⁻¹ ∈ K₂(N, B[t][y])`
die after padding, where `ψ : F_p[s_0..s_k] ≅ B[t]` sends `s_0 ↦ t`. -/
def PolyK2CubeNilLocalStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, k + 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin (k + 1)) (ZMod p)),
      (∀ i : Fin (k + 1), K2Map (cubeKill (ZMod p) i) u = 1) →
        ∀ m : Ideal (MvPolynomial (Fin k) (ZMod p)), m.IsMaximal →
          ∃ s : MvPolynomial (Fin k) (ZMod p), s ∉ m ∧
            K2DiesAfterPadding
              (quillenDiff (K2Map (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom u) s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2CubeNilLocalStatement

/-- **Endpoint**: the local gap gives the cube gap `PolyK2CubeNilStatement`. -/
theorem polyK2CubeNil_of_cubeLocal (h : PolyK2CubeNilLocalStatement) : PolyK2CubeNilStatement := by
  intro p hp k N hk hkN _ u hu
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
  have hev : K2Map (Polynomial.evalRingHom 0 :
      Polynomial (MvPolynomial (Fin j) (ZMod p)) →+* MvPolynomial (Fin j) (ZMod p))
        (K2Map (MvPolynomial.finSuccEquiv (ZMod p) j).toRingEquiv.toRingHom u) = 1 := by
    rw [K2Map_K2Map, ← evalZero_finSuccEquiv_comp_cubeKill_zero (R := ZMod p) j, ← K2Map_K2Map,
      hu 0, map_one]
  obtain ⟨M, hNM, hM⟩ := diesAfterPadding_of_local hev (h p hp j N (by omega) u hu)
  refine ⟨M, hNM, ?_⟩
  rw [← K2Map_K2Map_of_comp_eq_id _ _
      (MvPolynomial.finSuccEquiv (ZMod p) j).toRingEquiv.symm_toRingHom_comp_toRingHom u,
    K2IndexMap_K2Map, hM, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2CubeNil_of_cubeLocal

/-- Conversely, the cube gap gives the local gap, with `s = 1`. -/
theorem polyK2CubeNilLocal_of_cubeNil (h : PolyK2CubeNilStatement) :
    PolyK2CubeNilLocalStatement := by
  intro p hp k N hkN u hu _ hm
  refine ⟨1, (Ideal.ne_top_iff_one _).mp hm.ne_top, ?_⟩
  exact diesAfterPadding_quillenDiff_of_diesAfterPadding
    (diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom
      (h p hp (k + 1) N (Nat.succ_pos k) (by omega) (by omega) u hu)) 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2CubeNilLocal_of_cubeNil

/-- **Endpoint**: the local gap gives lane `bh-met-14`'s `PolyK2NilPosStatement`. -/
theorem polyK2NilPos_of_cubeLocal (h : PolyK2CubeNilLocalStatement) : PolyK2NilPosStatement :=
  polyK2NilPos_of_cubeNil (polyK2CubeNil_of_cubeLocal h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2NilPos_of_cubeLocal

/-- **Endpoint**: the local gap gives the frontier item `PolyK2OneVarNilStatement`. -/
theorem polyK2OneVarNil_of_cubeLocal (h : PolyK2CubeNilLocalStatement) :
    PolyK2OneVarNilStatement :=
  polyK2OneVarNil_of_cubeNil (polyK2CubeNil_of_cubeLocal h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2OneVarNil_of_cubeLocal

end GroupApproximation.BooneHigman.Metabelian.ElemFP
