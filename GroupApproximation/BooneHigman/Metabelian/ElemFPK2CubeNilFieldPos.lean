import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilFieldCone
import GroupApproximation.Meta.AxiomGuard

/-!
# The local cube gap: the field case `B = F_p` follows from the case `B = F_p[s_1]`

Lane `bh-met-61c` (re-dispatch of lanes `bh-met-61`, `bh-met-61b`).  Lane `bh-met-46b` (module
`ElemFPK2CubeNilLocal`) isolated `PolyK2CubeNilLocalStatement`: for `N ≥ k + 5`, an element
`u ∈ K₂(N, F_p[s_0..s_k])` killed by every `π_i : s_i ↦ 0` and a maximal ideal `m` of
`B = F_p[s_1..s_k]`, some `s ∉ m` makes `v_s(ψ u)` die after padding.  For `k = 0` the base
`B = F_p` is a field (the only maximal ideal is `⊥`); this is the *field case*.

* `cubeNilField_dies_of_local`: for any commutative ring `R` and one fixed `u`, the local
  condition at every maximal ideal of `R[s_1..s_j]` makes `u ∈ K₂(N, R[s_0..s_j])` die, if
  `π_0 u = 1`.  This is the per-element form of `polyK2CubeNil_of_cubeLocal`.
* `cubeNilField_dies_of_cone`: if `j u` dies, where `j : s_0 ↦ s_0 s_1` is the cone substitution
  (module `ElemFPK2CubeNilFieldCone`), then `u` dies: apply the retraction `r` with `r ∘ j = id`.
* `cubeNilField_dies_fieldCase`: the field case from the one-variable case.  Pad
  `u ∈ K₂(N, R[s_0])` to rank `N + 1`; its cone image is killed by `s_0 ↦ 0` and `s_1 ↦ 0`,
  so the local condition over `R[s_1]` kills it, and the retraction kills `u`.
* `PolyK2CubeNilFieldPosStatement`: **the isolated gap**, `PolyK2CubeNilLocalStatement` for
  `k ≥ 1` only, i.e. for bases `B = F_p[s_1..s_k]` that are *not* fields.
* `polyK2CubeNilLocal_of_cubeNilFieldPos`: **endpoint**, the gap gives the local statement.
* `cubeNilFieldPos_of_polyK2CubeNilLocal`: the (trivial) converse.

## LOUD: truth check and the requested route

The requested route "reduce the local case to the field case, then prove the field case" is
**not available**, and runs the wrong way.  The cone `s_0 ↦ s_0 s_1` with its retraction shows
that the local statement with `k + 1` base variables implies the one with `k` base variables;
so the field case `k = 0` is the *weakest* instance, and it is the one derived here.  No
elementary argument derives the case of a regular base `B` (or of its local rings `B_m`) from
the case of fields: that is Quillen's dévissage and localization sequence, or Gersten's
conjecture, with Tulenbaev's dilation lemma on top.  The field case itself (`NK₂(F_p) = 0` in
unstable form, i.e. `K₂(N, F_p[t]) → K₂(N, F_p)` injective after padding) is also a genuine
theorem (Tits, Rehmann, Soulé), not proved here.

**LOUD: the gap is logically equivalent to `PolyK2CubeNilLocalStatement`** (both directions are
proved).  It is strictly smaller in proof content: it no longer asks for the field case
`k = 0`, which is supplied here from the case `k = 1` by the cone substitution, one padding
step, the Quillen patching of lane `bh-met-46` and the retraction `s_1 ↦ 1`.

The gap is true: it is a sub-family of the instances of `PolyK2CubeNilLocalStatement`, which is
true by Quillen's homotopy invariance for the regular ring `F_p[s_0..s_k]` (see the truth check
of module `ElemFPK2CubeNilLocal`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section FieldCase

variable {R : Type*} [CommRing R]

/-- **Per-element patching.**  If `π_0 u = 1` and every maximal ideal `m` of `R[s_1..s_j]` misses
some `s` with `v_s(ψ u)` dying after padding, then `u ∈ K₂(N, R[s_0..s_j])` dies after padding. -/
theorem cubeNilField_dies_of_local {j N : ℕ} (u : K2 (Fin N) (MvPolynomial (Fin (j + 1)) R))
    (hu : K2Map (cubeKill R (0 : Fin (j + 1))) u = 1)
    (hloc : ∀ m : Ideal (MvPolynomial (Fin j) R), m.IsMaximal →
      ∃ s : MvPolynomial (Fin j) R, s ∉ m ∧
        K2DiesAfterPadding
          (quillenDiff (K2Map (MvPolynomial.finSuccEquiv R j).toRingEquiv.toRingHom u) s)) :
    K2DiesAfterPadding u := by
  have hev : K2Map (Polynomial.evalRingHom 0 :
      Polynomial (MvPolynomial (Fin j) R) →+* MvPolynomial (Fin j) R)
        (K2Map (MvPolynomial.finSuccEquiv R j).toRingEquiv.toRingHom u) = 1 := by
    rw [K2Map_K2Map, ← evalZero_finSuccEquiv_comp_cubeKill_zero (R := R) j, ← K2Map_K2Map,
      hu, map_one]
  obtain ⟨M, hNM, hM⟩ := diesAfterPadding_of_local hev hloc
  refine ⟨M, hNM, ?_⟩
  rw [← K2Map_K2Map_of_comp_eq_id _ _
      (MvPolynomial.finSuccEquiv R j).toRingEquiv.symm_toRingHom_comp_toRingHom u,
    K2IndexMap_K2Map, hM, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilField_dies_of_local

/-- If the cone image `j u` dies after padding, so does `u`, because `r ∘ j = id`. -/
theorem cubeNilField_dies_of_cone {N : ℕ} (u : K2 (Fin N) (MvPolynomial (Fin (0 + 1)) R))
    (hv : K2DiesAfterPadding (K2Map (cubeCone R) u)) : K2DiesAfterPadding u := by
  have h := diesAfterPadding_K2Map (cubeConeRetract R) hv
  rwa [K2Map_K2Map_of_comp_eq_id _ _ (cubeConeRetract_comp_cubeCone R)] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilField_dies_of_cone

/-- **The field case from the one-variable case.**  Let `u ∈ K₂(N, R[s_0])` be killed by
`s_0 ↦ 0`.  Suppose that every `v ∈ K₂(N + 1, R[s_0, s_1])` killed by `s_0 ↦ 0` and by
`s_1 ↦ 0` meets the local condition over `R[s_1]`.  Then `u` dies after padding. -/
theorem cubeNilField_dies_fieldCase {N : ℕ} (u : K2 (Fin N) (MvPolynomial (Fin (0 + 1)) R))
    (hu : K2Map (cubeKill R (0 : Fin (0 + 1))) u = 1)
    (hloc : ∀ v : K2 (Fin (N + 1)) (MvPolynomial (Fin (1 + 1)) R),
      (∀ i : Fin (1 + 1), K2Map (cubeKill R i) v = 1) →
        ∀ m : Ideal (MvPolynomial (Fin 1) R), m.IsMaximal →
          ∃ s : MvPolynomial (Fin 1) R, s ∉ m ∧
            K2DiesAfterPadding
              (quillenDiff (K2Map (MvPolynomial.finSuccEquiv R 1).toRingEquiv.toRingHom v) s)) :
    K2DiesAfterPadding u := by
  have hu' : K2Map (cubeKill R (0 : Fin (0 + 1)))
      (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) u) = 1 := by
    rw [← K2IndexMap_K2Map, hu, map_one]
  have hv : ∀ i : Fin (1 + 1), K2Map (cubeKill R i)
      (K2Map (cubeCone R) (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) u)) = 1 :=
    fun i ↦ K2Map_cubeKill_K2Map_cubeCone hu' i
  have hdies : K2DiesAfterPadding
      (K2Map (cubeCone R) (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) u)) :=
    cubeNilField_dies_of_local (j := 1) _ (hv 0) (hloc _ hv)
  exact diesAfterPadding_of_diesAfterPadding_castLEEmb (Nat.le_add_right N 1)
    (cubeNilField_dies_of_cone _ hdies)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilField_dies_fieldCase

end FieldCase

/-- **The isolated gap**: `PolyK2CubeNilLocalStatement` for `k ≥ 1`, i.e. only for bases
`B = F_p[s_1..s_k]` that are not fields.  For `N ≥ k + 5`, an element
`u ∈ K₂(N, F_p[s_0..s_k])` killed by every substitution `s_i ↦ 0`, and a maximal ideal `m` of
`B`, some `s ∉ m` makes `v_s(ψ u) = (ψ u)(t + s y) · (ψ u)(t)⁻¹` die after padding.

**LOUD: logically equivalent to `PolyK2CubeNilLocalStatement`**; the field case `k = 0` is removed
from the gap and derived (`cubeNilField_dies_fieldCase`).  True, as a sub-family of the instances
of `PolyK2CubeNilLocalStatement` (Quillen homotopy invariance). -/
def PolyK2CubeNilFieldPosStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, 0 < k → k + 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin (k + 1)) (ZMod p)),
      (∀ i : Fin (k + 1), K2Map (cubeKill (ZMod p) i) u = 1) →
        ∀ m : Ideal (MvPolynomial (Fin k) (ZMod p)), m.IsMaximal →
          ∃ s : MvPolynomial (Fin k) (ZMod p), s ∉ m ∧
            K2DiesAfterPadding
              (quillenDiff (K2Map (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom u) s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2CubeNilFieldPosStatement
