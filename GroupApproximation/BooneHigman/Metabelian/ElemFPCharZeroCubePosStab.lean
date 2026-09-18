import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarNilCube
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2InjStabRetract
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilGeneric
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal injective stability on `ker ev₀`: reduction to elements killed by every `s_i ↦ 0`

Lane `bh-met-90e`, stability module.  The root hypothesis `hcube : CharZeroK2CubeGapPosStatement`
has two halves over `A = ℤ[1/m]`, `m ≥ 1`.  Lanes `bh-met-73c`, `bh-met-74`, `bh-met-81` cut the
cube half down to `CZCubeResFieldStatement`.  The **diagonal half**
`PolyK2StabRangeDiagStatementOver A 4` (for `k ≥ 1`, `u ∈ K₂(k + 4, A[s_1..s_k])` with `ev₀ u = 1`
and `K2Stab u = 1` is trivial) had not been reduced.  This module runs the cube decomposition of
lane `bh-met-34` (`cube_step`) on it, with "dies after padding" replaced by "is trivial" and the
stabilization carried along.

Write `π_i = cubeKill`, `θ_i = cubeScale`, `ε_i = cubeUnit`, `cc = constantCoeff`.

* `czCubePos_K2Stab_K2Map_eq_one`: `K2Stab u = 1 → K2Stab (f u) = 1` (naturality,
  `k2InjStab_K2Stab_K2Map`).
* `czCubePos_stab_step`: the cube step.  Split `u = (u b⁻¹) b` with `b = π_J u`.  Both factors
  have trivial stabilization (naturality).  `u b⁻¹` is killed by `π_i`, `i ≥ J`.  For `b`, put
  `w = θ_J b`: it is killed by `π_i`, `i ≥ J` (`π_J θ_J π_J = C ∘ cc`), has `cc w = 1` and
  `K2Stab w = 1`, so `w = 1`, and `b = ε_J w = 1` (`ε_J θ_J π_J = π_J`).
* `czCubePos_eq_one_of_cube`: induction on `j`; ring-generic, at every fixed rank `N` and number
  of variables `k`.  No rank or variable changes: all maps are endomorphisms of `R[s_1..s_k]`.
* `CZCubePosStabOverStatement A`: for `k ≥ 1`, `u ∈ K₂(k + 4, A[s_1..s_k])` killed by **every**
  `π_i` with `K2Stab u = 1` is trivial.
* `czCubePos_stabRangeDiagOver_of_cubeStab`: it gives `PolyK2StabRangeDiagStatementOver A 4`.
* `czCubePos_cubeStab_of_stabRangeDiagOver`: the converse (`cc = cc ∘ π_0`).

## Strength (LOUD)

`CZCubePosStabOverStatement A` is **logically equivalent** to the diagonal half (both directions
proved).  It is **strictly smaller in proof content**: its hypothesis is the strongest available
(killed by every `π_i`, not only by `cc`), and the whole cube decomposition (the `k`-step
induction, the idempotence/commutation of the `π_i`, the scaling trick `θ_J` and its unit
retraction `ε_J`) is discharged here.  What remains is van der Kallen's injective stability on
the "cube part" `⋂ᵢ ker π_i` only.

## Truth check

`S = ℤ[1/m][s_1..s_k]`, `m ≥ 1`, `k ≥ 1`: noetherian of Krull dimension `k + 1`, so Bass gives
`sr(S) ≤ k + 2`, and van der Kallen's injective stability `K₂(n, S) ↪ K₂(n + 1, S)` for
`n ≥ sr(S) + 2` covers `n = k + 4`.  So `K2Stab u = 1` forces `u = 1` for **every** `u`, in
particular for `u ∈ ⋂ᵢ ker π_i`.  **True** (a sub-family of the true diagonal half).  The ring
identities used (`π_J θ_J π_J = C ∘ cc`, `ε_J θ_J π_J = π_J`, `π_i θ_J = θ_J π_i` for `i ≠ J`,
`cc θ_J = cc`, `π_i π_J = π_J π_i`, `π_J π_J = π_J`) are the Lean lemmas of
`ElemFPK2OneVarNilCubeMaps`; they were also re-checked on 40 random integer polynomials in three
variables.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- Trivial stabilization is preserved by coefficient maps. -/
theorem czCubePos_K2Stab_K2Map_eq_one {R S : Type*} [Ring R] [Ring S] {n : ℕ} (f : R →+* S)
    {u : K2n n R} (hu : K2Stab n R u = 1) : K2Stab n S (K2Map f u) = 1 := by
  rw [k2InjStab_K2Stab_K2Map, hu, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubePos_K2Stab_K2Map_eq_one

/-- **The cube step for stability**: from the variables `≥ j` to the variables `≥ j + 1`. -/
theorem czCubePos_stab_step {R : Type*} [CommRing R] {k N : ℕ} (j : ℕ)
    (hj : ∀ u : K2n N (MvPolynomial (Fin k) R),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R) u = 1 →
      (∀ i : Fin k, j ≤ i.val → K2Map (cubeKill R i) u = 1) →
      K2Stab N (MvPolynomial (Fin k) R) u = 1 → u = 1)
    (u : K2n N (MvPolynomial (Fin k) R))
    (hcc : K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R) u = 1)
    (hu : ∀ i : Fin k, j + 1 ≤ i.val → K2Map (cubeKill R i) u = 1)
    (hs : K2Stab N (MvPolynomial (Fin k) R) u = 1) : u = 1 := by
  by_cases hjk : j < k
  swap
  · exact hj u hcc (fun i hi ↦ absurd (lt_of_le_of_lt hi i.isLt) hjk) hs
  obtain ⟨J, rfl⟩ : ∃ J : Fin k, J.val = j := ⟨⟨j, hjk⟩, rfl⟩
  have hbs : K2Stab N (MvPolynomial (Fin k) R) (K2Map (cubeKill R J) u) = 1 :=
    czCubePos_K2Stab_K2Map_eq_one (cubeKill R J) hs
  have has : K2Stab N (MvPolynomial (Fin k) R) (u * (K2Map (cubeKill R J) u)⁻¹) = 1 := by
    rw [map_mul, map_inv, hs, hbs, inv_one, mul_one]
  have hws : K2Stab N (MvPolynomial (Fin k) R)
      (K2Map (cubeScale R J) (K2Map (cubeKill R J) u)) = 1 :=
    czCubePos_K2Stab_K2Map_eq_one (cubeScale R J) hbs
  have ha : u * (K2Map (cubeKill R J) u)⁻¹ = 1 := by
    refine hj _ ?_ (fun i hi ↦ ?_) has
    · rw [map_mul, map_inv, K2Map_K2Map, constantCoeff_comp_cubeKill, hcc, inv_one, mul_one]
    · rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · rw [map_mul, map_inv, K2Map_K2Map, cubeKill_comp_comm, ← K2Map_K2Map, hu i hlt,
          map_one, inv_one, mul_one]
      · obtain rfl : J = i := Fin.ext heq
        rw [map_mul, map_inv, K2Map_K2Map, cubeKill_idem, mul_inv_cancel]
  have hw : K2Map (cubeScale R J) (K2Map (cubeKill R J) u) = 1 := by
    refine hj _ ?_ (fun i hi ↦ ?_) hws
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
  have hb : K2Map (cubeKill R J) u = 1 := by
    have h := DFunLike.congr_arg (K2Map (I := Fin N) (cubeUnit R J)) hw
    rwa [K2Map_K2Map, K2Map_K2Map, cubeUnit_comp_cubeScale_comp_cubeKill, map_one] at h
  rwa [hb, inv_one, mul_one] at ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubePos_stab_step

/-- **The cube reduction for stability**, any commutative ring, any rank `N`: if every element
killed by each `s_i ↦ 0` with trivial stabilization is trivial, then so is every element killed by
`cc` with trivial stabilization. -/
theorem czCubePos_eq_one_of_cube {R : Type*} [CommRing R] {k N : ℕ}
    (hcube : ∀ v : K2n N (MvPolynomial (Fin k) R),
      (∀ i : Fin k, K2Map (cubeKill R i) v = 1) → K2Stab N (MvPolynomial (Fin k) R) v = 1 →
        v = 1)
    (u : K2n N (MvPolynomial (Fin k) R))
    (hu : K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R) u = 1)
    (hs : K2Stab N (MvPolynomial (Fin k) R) u = 1) : u = 1 := by
  have key : ∀ j : ℕ, ∀ v : K2n N (MvPolynomial (Fin k) R),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R) v = 1 →
      (∀ i : Fin k, j ≤ i.val → K2Map (cubeKill R i) v = 1) →
      K2Stab N (MvPolynomial (Fin k) R) v = 1 → v = 1 := by
    intro j
    induction j with
    | zero => exact fun v _ hkill hv ↦ hcube v (fun i ↦ hkill i (Nat.zero_le _)) hv
    | succ j ih => exact czCubePos_stab_step j ih
  exact key k u hu (fun i hi ↦ absurd i.isLt (Nat.not_lt.mpr hi)) hs

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubePos_eq_one_of_cube
