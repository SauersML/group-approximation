import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarNilCubeMaps
import GroupApproximation.Meta.AxiomGuard

/-!
# The nil part of `K₂(N, R[s_1..s_k])`: reduction to elements killed by every `s_i ↦ 0`

Lane `bh-met-34`.  Write `A = R[s_1..s_k]`, `cc : A → R` for the constant coefficient,
`π_i = cubeKill R i`, `θ_i = cubeScale R i` and `ε_i = cubeUnit R i`.

* `K2DiesAfterPadding u`: `u` dies after padding.  This property is closed under products
  (`diesAfterPadding_mul`, pad both factors to the maximum rank) and under ring maps
  (`diesAfterPadding_K2Map`, by naturality `K2IndexMap_K2Map`).
* `cube_step`: suppose that `cc u = 1` together with `π_i u = 1` for all `i ≥ j` implies that
  `u` dies.  Then the same holds for `j + 1`.  Put `J = j` (when `j ≥ k` there is nothing to
  show) and `b = π_J u`, and split `u = (u b⁻¹) b`.
  - `u b⁻¹` is killed by `π_J`, because `π_J` is idempotent.  For `i > J` it is killed by `π_i`,
    because `π_i` commutes with `π_J`.  Its constant coefficient is `1`.  So it dies by hypothesis.
  - Put `w = θ_J b`.  Then `π_J w = C (cc u) = 1`.  For `i > J`, `π_i w = θ_J π_J π_i u = 1`.
    Also `cc w = cc u = 1`.  So `w` dies, hence so does `ε_J w = ε_J θ_J π_J u = b`.
* `nil_of_cube`: induction on `j`.  The case `j = 0` is the cube hypothesis and `j = k` is the nil
  part.
* `PolyK2CubeNilStatement`: the gap left over.  For `k ≥ 1`, `N ≥ k + 4`, `N ≥ 5`, an element of
  `K₂(N, F_p[s_1..s_k])` that is killed by each `s_i ↦ 0` dies after padding.
* `polyK2NilPos_of_cubeNil`, `polyK2OneVarNil_of_cubeNil`, `polynomialFpK2Vanishing_of_cubeNil`:
  the endpoints.  `polyK2CubeNil_of_nilPos` is the converse: the hypothesis `∀ i, π_i u = 1`
  implies `cc u = 1`, because `cc = cc ∘ π_0`.

Truth of the gap.  It follows from `PolyK2NilPosStatement`, which Quillen homotopy invariance
(`NK₂` of a regular ring vanishes) together with the colimit description of stable `K₂` makes true.
No rank bound is needed.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- `u ∈ K₂(N, R)` dies after padding to some finite rank `M ≥ N`. -/
def K2DiesAfterPadding {R : Type*} [Ring R] {N : ℕ} (u : K2 (Fin N) R) : Prop :=
  ∃ M : ℕ, ∃ hNM : N ≤ M, K2IndexMap (R := R) (Fin.castLEEmb hNM) u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2DiesAfterPadding

theorem diesAfterPadding_mul {R : Type*} [Ring R] {N : ℕ} {u v : K2 (Fin N) R}
    (hu : K2DiesAfterPadding u) (hv : K2DiesAfterPadding v) : K2DiesAfterPadding (u * v) := by
  obtain ⟨M₁, h₁, hM₁⟩ := hu
  obtain ⟨M₂, h₂, hM₂⟩ := hv
  have hN : N ≤ max M₁ M₂ := h₁.trans (le_max_left M₁ M₂)
  refine ⟨max M₁ M₂, hN, ?_⟩
  rw [map_mul, K2IndexMap_eq_one_of_le h₁ (le_max_left M₁ M₂) hN hM₁,
    K2IndexMap_eq_one_of_le h₂ (le_max_right M₁ M₂) hN hM₂, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_mul

theorem diesAfterPadding_K2Map {R S : Type*} [Ring R] [Ring S] {N : ℕ} (f : R →+* S)
    {u : K2 (Fin N) R} (hu : K2DiesAfterPadding u) : K2DiesAfterPadding (K2Map f u) := by
  obtain ⟨M, hNM, hM⟩ := hu
  exact ⟨M, hNM, by rw [K2IndexMap_K2Map, hM, map_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_K2Map

/-- **The cube step**: from the variables `≥ j` to the variables `≥ j + 1`. -/
theorem cube_step {R : Type*} [CommRing R] {k N : ℕ} (j : ℕ)
    (hj : ∀ u : K2 (Fin N) (MvPolynomial (Fin k) R),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R) u = 1 →
      (∀ i : Fin k, j ≤ i.val → K2Map (cubeKill R i) u = 1) → K2DiesAfterPadding u)
    (u : K2 (Fin N) (MvPolynomial (Fin k) R))
    (hcc : K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R) u = 1)
    (hu : ∀ i : Fin k, j + 1 ≤ i.val → K2Map (cubeKill R i) u = 1) :
    K2DiesAfterPadding u := by
  by_cases hjk : j < k
  swap
  · exact hj u hcc fun i hi ↦ absurd (lt_of_le_of_lt hi i.isLt) hjk
  obtain ⟨J, rfl⟩ : ∃ J : Fin k, J.val = j := ⟨⟨j, hjk⟩, rfl⟩
  have ha : K2DiesAfterPadding (u * (K2Map (cubeKill R J) u)⁻¹) := by
    refine hj _ ?_ fun i hi ↦ ?_
    · rw [map_mul, map_inv, K2Map_K2Map, constantCoeff_comp_cubeKill, hcc, inv_one, mul_one]
    · rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · rw [map_mul, map_inv, K2Map_K2Map, cubeKill_comp_comm, ← K2Map_K2Map, hu i hlt,
          map_one, inv_one, mul_one]
      · obtain rfl : J = i := Fin.ext heq
        rw [map_mul, map_inv, K2Map_K2Map, cubeKill_idem, mul_inv_cancel]
  have hw : K2DiesAfterPadding (K2Map (cubeScale R J) (K2Map (cubeKill R J) u)) := by
    refine hj _ ?_ fun i hi ↦ ?_
    · rw [K2Map_K2Map, K2Map_K2Map, constantCoeff_comp_cubeScale, constantCoeff_comp_cubeKill,
        hcc]
    · rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · have hne : i ≠ J := fun h ↦ by
          subst h
          exact Nat.lt_irrefl _ hlt
        rw [K2Map_K2Map, K2Map_K2Map, cubeKill_comp_cubeScale_of_ne hne, RingHom.comp_assoc,
          cubeKill_comp_comm, ← K2Map_K2Map, ← K2Map_K2Map, hu i hlt, map_one, map_one]
      · obtain rfl : J = i := Fin.ext heq
        rw [K2Map_K2Map, K2Map_K2Map, cubeKill_comp_cubeScale, RingHom.comp_assoc,
          constantCoeff_comp_cubeKill, ← K2Map_K2Map, hcc, map_one]
  have hb : K2DiesAfterPadding (K2Map (cubeKill R J) u) := by
    have h := diesAfterPadding_K2Map (cubeUnit R J) hw
    rwa [K2Map_K2Map, K2Map_K2Map, cubeUnit_comp_cubeScale_comp_cubeKill] at h
  have h := diesAfterPadding_mul ha hb
  rwa [inv_mul_cancel_right] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cube_step

/-- **The cube reduction**: if every element killed by each `s_i ↦ 0` dies after padding, then
every element killed by `cc` dies after padding. -/
theorem nil_of_cube {R : Type*} [CommRing R] {k N : ℕ}
    (hcube : ∀ u : K2 (Fin N) (MvPolynomial (Fin k) R),
      (∀ i : Fin k, K2Map (cubeKill R i) u = 1) → K2DiesAfterPadding u)
    (u : K2 (Fin N) (MvPolynomial (Fin k) R))
    (hu : K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R) u = 1) :
    K2DiesAfterPadding u := by
  have key : ∀ j : ℕ, ∀ v : K2 (Fin N) (MvPolynomial (Fin k) R),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R) v = 1 →
      (∀ i : Fin k, j ≤ i.val → K2Map (cubeKill R i) v = 1) → K2DiesAfterPadding v := by
    intro j
    induction j with
    | zero => exact fun v _ hkill ↦ hcube v fun i ↦ hkill i (Nat.zero_le _)
    | succ j ih => exact cube_step j ih
  exact key k u hu fun i hi ↦ absurd i.isLt (Nat.not_lt.mpr hi)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.nil_of_cube

/-- **The isolated gap**: for `k ≥ 1`, `N ≥ k + 4`, `N ≥ 5`, an element of
`K₂(N, F_p[s_1..s_k])` killed by each substitution `s_i ↦ 0` dies after padding. -/
def PolyK2CubeNilStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, 0 < k → k + 4 ≤ N → 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) (ZMod p)),
      (∀ i : Fin k, K2Map (cubeKill (ZMod p) i) u = 1) →
        ∃ M : ℕ, ∃ hNM : N ≤ M,
          K2IndexMap (R := MvPolynomial (Fin k) (ZMod p)) (Fin.castLEEmb hNM) u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2CubeNilStatement

/-- **Endpoint**: the cube gap gives `PolyK2NilPosStatement`. -/
theorem polyK2NilPos_of_cubeNil (h : PolyK2CubeNilStatement) : PolyK2NilPosStatement :=
  fun p hp k N hk hkN h5N u hu ↦
    nil_of_cube (R := ZMod p) (k := k) (N := N) (fun v hv ↦ h p hp k N hk hkN h5N v hv) u hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2NilPos_of_cubeNil

/-- Conversely, `PolyK2NilPosStatement` gives the cube gap, because `cc = cc ∘ π_0`. -/
theorem polyK2CubeNil_of_nilPos (h : PolyK2NilPosStatement) : PolyK2CubeNilStatement := by
  intro p hp k N hk hkN h5N u hu
  refine h p hp k N hk hkN h5N u ?_
  rw [← constantCoeff_comp_cubeKill (R := ZMod p) (⟨0, hk⟩ : Fin k), ← K2Map_K2Map,
    hu ⟨0, hk⟩, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2CubeNil_of_nilPos

/-- **Endpoint**: the cube gap gives the one-variable gap `PolyK2OneVarNilStatement`. -/
theorem polyK2OneVarNil_of_cubeNil (h : PolyK2CubeNilStatement) : PolyK2OneVarNilStatement :=
  polyK2OneVarNil_of_nilPos (polyK2NilPos_of_cubeNil h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2OneVarNil_of_cubeNil

/-- **Combined endpoint**: the stability gap, the cube gap and the field case give
`K₂(N, F_p[s_1..s_k]) = 0` for `N ≥ k + 4`, `N ≥ 5`. -/
theorem polynomialFpK2Vanishing_of_cubeNil (hstab : PolyK2NilStabilityPosStatement)
    (hcube : PolyK2CubeNilStatement) (hfield : FieldK2VanishingStatement) :
    PolynomialFpK2VanishingStatement :=
  polynomialFpK2Vanishing_of_nilPos hstab (polyK2NilPos_of_cubeNil hcube) hfield

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polynomialFpK2Vanishing_of_cubeNil

end GroupApproximation.BooneHigman.Metabelian.ElemFP
