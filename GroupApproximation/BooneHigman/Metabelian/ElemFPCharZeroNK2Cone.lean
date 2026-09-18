import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroCubePosEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The minimal-rank char-zero cube gap, cut down to cone images

Lane `bh-met-90g`.  Lane `bh-met-81` isolated `CZCubeResFieldStatement`: over `A = ℤ[1/m]`, for
`k ≥ 1`, every `u ∈ K₂(k + 5, A[s_0..s_k])` killed by every `π_i : s_i ↦ 0`, and every maximal
`𝔪 ∋ p` of `B = A[s_1..s_k]`, some `s ∉ 𝔪` makes the Quillen difference `v_s(ψ u)` die after
padding.

This module shrinks the family of elements on which that local condition has to be checked.

* `czNK2_ConeOverStatement A`: the local condition, but only for the **cone images**
  `w = j(ι v)`, where `v ∈ K₂(n + 5, A[s_0..s_n])` is killed by every `π_i`, `ι` pads the rank
  once to `n + 6`, and `j : s_0 ↦ s_0 s_{n+1}` is the cone of module
  `ElemFPCharZeroK2CubeResidueFieldCone`.  These `w` live at `k = n + 1` base variables and the minimal rank `n + 6 = k + 5`.
* `czNK2_dies_of_coneOver`: every cube element `v` at rank `n + 5` dies after padding.  Quillen
  patching (`cubeNilField_dies_of_local`) kills `w`, using `hres` (every maximal ideal contains a
  rational prime) to reach the residual; the retraction `s_{n+1} ↦ 1` of the cone carries the death
  to `ι v`, and the padding carries it to `v`.
* `czNK2_resFieldOver_of_coneOver` and `czNK2_coneOver_of_resFieldOver` are the reduction and its
  converse over one `A`.
* `czNK2_ConeStatement`: the cone residual over every `ℤ[1/m]`, `m ≥ 1`.  **The isolated gap.**
* The endpoints are `czNK2_resField_of_cone` (the lane target `CZCubeResFieldStatement`),
  `czNK2_residue_of_cone` (`CZCubeLocalResidueStatement`) and `czNK2_gapPos_of_cone_of_cubeStab`
  (the root hypothesis `CharZeroK2CubeGapPosStatement`, given the stability half).

## LOUD: strength, and why the target is not closed

`czNK2_ConeStatement` is **logically equivalent** to `CZCubeResFieldStatement`; both directions are
proved below.  No statement `S` with `S → CZCubeResFieldStatement` proved can be strictly weaker
logically.  The residual is **strictly smaller in proof content**: it is the sub-family of
`CZCubeResFieldOverStatement` at `(k, N) = (n + 1, n + 6)` made of the elements `j(ι v)`.  Those
elements come from one rank lower (`n + 5`), depend on `s_0` only through `s_0 s_{last}`, and are
also killed by `s_{last} ↦ 0`.  The local condition on every other cube element at minimal rank
is derived here: each such `u` (at `k` base variables) is itself a `v` with `n = k`, so it dies.

The target is **not** proved.  Its content is Quillen's `NK₂ = 0` for the regular ring
`ℤ[1/m][s_1..s_k]`, locally at `𝔪`.  Every `B_𝔪` here has Krull dimension at least 2, so there
is no field or DVR sub-case to prove outright.  The Swan–Weibel dilation `t ↦ c t` does not
reduce the cone case either.  At `𝔪 ∌ s_{last}` it only rewrites `v_a(μ_c g)` as a pushforward of
`v_{ca}(g)`, which is the same local question for `ι v` at a non-minimal rank, so the argument is
circular.  At `𝔪 ∋ s_{last}` it gives nothing new.  No residual is claimed to follow from
`NK₂ = 0` under another name, and no literature input is used.

## Truth check

The residual is true.  It is a sub-family (converse proved) of `CZCubeResFieldOverStatement`, and
by Quillen `NK₂(ℤ[1/m][s_1..s_k]) = 0`.  So `w`, which is killed by `ev₀`, is stably trivial and
dies at a finite rank, and then `s = 1` meets the local demand.  Smallest instance: `n = 0`, so
`v ∈ K₂(5, A[s_0])` with `π_0 v = 1` and `w = v(s_0 s_1)` at rank 6.  Here `B = A[s_1]`,
`𝔪 = (p, f(s_1))` with `f` irreducible mod `p`, and `v = 1` because `NK₂(A) = 0`.  The ring
identities used (`r ∘ j = id`, `π_i ∘ j = j ∘ π_i`, `π_last ∘ j = j ∘ π_0`) are proved in
`ElemFPCharZeroK2CubeResidueFieldCone`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Over

variable (A : Type*) [CommRing A]

/-- **The cone residual over `A`.**  The local cube condition of `CZCubeResFieldOverStatement A`,
only for the cone images `j(ι v)` of cube elements `v` at rank `n + 5`: here `k = n + 1` base
variables and rank `n + 6`. -/
def czNK2_ConeOverStatement : Prop :=
  ∀ n N : ℕ, N = n + 5 →
    ∀ v : K2n N (MvPolynomial (Fin (n + 1)) A),
      (∀ i : Fin (n + 1), K2Map (cubeKill A i) v = 1) →
        ∀ p : ℕ, p.Prime →
          ∀ P : Ideal (MvPolynomial (Fin (n + 1)) A), P.IsMaximal →
            (p : MvPolynomial (Fin (n + 1)) A) ∈ P →
              ∃ s : MvPolynomial (Fin (n + 1)) A, s ∉ P ∧
                K2DiesAfterPadding
                  (quillenDiff
                    (K2Map (MvPolynomial.finSuccEquiv A (n + 1)).toRingEquiv.toRingHom
                      (K2Map (czCubeResFieldCone A n)
                        (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v))) s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czNK2_ConeOverStatement

/-- Padding once keeps an element killed by every `π_i`. -/
theorem czNK2_cubeKill_pad {n N : ℕ} {v : K2n N (MvPolynomial (Fin (n + 1)) A)}
    (hv : ∀ i : Fin (n + 1), K2Map (cubeKill A i) v = 1) (i : Fin (n + 1)) :
    K2Map (cubeKill A i) (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v) = 1 := by
  rw [← K2IndexMap_K2Map (Fin.castLEEmb (Nat.le_add_right N 1)) (cubeKill A i) v, hv i, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czNK2_cubeKill_pad

/-- **Death from the cone residual.**  If every maximal ideal of every `A[s_1..s_k]` contains a
prime, the cone residual makes every `v ∈ K₂(n + 5, A[s_0..s_n])` killed by every `π_i` die after
padding.  Patch `j(ι v)` (killed by `π_0`) with the residual, retract by `s_{n+1} ↦ 1`, unpad. -/
theorem czNK2_dies_of_coneOver
    (hres : ∀ k : ℕ, ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
      ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) A) ∈ P)
    (h : czNK2_ConeOverStatement A) {n N : ℕ} (hN : N = n + 5)
    (v : K2n N (MvPolynomial (Fin (n + 1)) A))
    (hv : ∀ i : Fin (n + 1), K2Map (cubeKill A i) v = 1) : K2DiesAfterPadding v := by
  have hw := czCubeResField_K2Map_cubeKill_cone (czNK2_cubeKill_pad A hv)
  have hdw : K2DiesAfterPadding (K2Map (czCubeResFieldCone A n)
      (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v)) :=
    cubeNilField_dies_of_local _ (hw 0) fun P hP ↦ by
      obtain ⟨p, hp, hpP⟩ := hres (n + 1) P hP
      exact h n N hN v hv p hp P hP hpP
  have hd := diesAfterPadding_K2Map (czCubeResFieldConeRetract A n) hdw
  rw [K2Map_K2Map_of_comp_eq_id _ _ (czCubeResField_retract_comp_cone A n)] at hd
  exact diesAfterPadding_of_diesAfterPadding_castLEEmb (Nat.le_add_right N 1) hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czNK2_dies_of_coneOver

/-- **The reduction over `A`.**  The cone residual gives the minimal-rank gap: at `k` base
variables and rank `N = k + 5`, `u` itself is a cube element at rank `k + 5`, so it dies, and
`s = 1 ∉ 𝔪` works. -/
theorem czNK2_resFieldOver_of_coneOver
    (hres : ∀ k : ℕ, ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
      ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) A) ∈ P)
    (h : czNK2_ConeOverStatement A) : CZCubeResFieldOverStatement A := by
  intro k N _ hN u hu _ _ P hP _
  refine ⟨1, (Ideal.ne_top_iff_one _).mp hP.ne_top, ?_⟩
  exact diesAfterPadding_quillenDiff_of_diesAfterPadding
    (diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom
      (czNK2_dies_of_coneOver A hres h hN u hu)) 1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czNK2_resFieldOver_of_coneOver

/-- Conversely, the minimal-rank gap gives the cone residual: `j(ι v)` is a cube element at
`k = n + 1` base variables and rank `n + 6 = k + 5`. -/
theorem czNK2_coneOver_of_resFieldOver (h : CZCubeResFieldOverStatement A) :
    czNK2_ConeOverStatement A := by
  intro n N hN v hv p hp P hP hpP
  exact h (n + 1) (N + 1) (Nat.succ_pos n) (by omega) _
    (czCubeResField_K2Map_cubeKill_cone (czNK2_cubeKill_pad A hv)) p hp P hP hpP

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czNK2_coneOver_of_resFieldOver

end Over

/-- **The isolated gap** (lane `bh-met-90g`): the cone residual over every `ℤ[1/m]`, `m ≥ 1`.
LOUD: logically equivalent to `CZCubeResFieldStatement`, strictly smaller in proof content (only
cone images of padded cube elements; see the module docstring). -/
def czNK2_ConeStatement : Prop :=
  ∀ m : ℕ, 0 < m → czNK2_ConeOverStatement (Localization.Away (m : ℤ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czNK2_ConeStatement

/-- **Endpoint (lane `bh-met-90g`).**  The cone residual gives `CZCubeResFieldStatement`. -/
theorem czNK2_resField_of_cone (h : czNK2_ConeStatement) : CZCubeResFieldStatement :=
  fun m hm ↦ czNK2_resFieldOver_of_coneOver _
    (fun _ P hP ↦ czCubeLocal_exists_prime_mem (m : ℤ) P hP) (h m hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czNK2_resField_of_cone

/-- Conversely, `CZCubeResFieldStatement` gives the cone residual. -/
theorem czNK2_cone_of_resField (h : CZCubeResFieldStatement) : czNK2_ConeStatement :=
  fun m hm ↦ czNK2_coneOver_of_resFieldOver _ (h m hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czNK2_cone_of_resField

/-- The cone residual gives the full residue statement `CZCubeLocalResidueStatement`. -/
theorem czNK2_residue_of_cone (h : czNK2_ConeStatement) : CZCubeLocalResidueStatement :=
  czCubeResField_residue_of_resField (czNK2_resField_of_cone h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czNK2_residue_of_cone

/-- The cone residual and cube-part stability give the root hypothesis
`CharZeroK2CubeGapPosStatement`. -/
theorem czNK2_gapPos_of_cone_of_cubeStab (h : czNK2_ConeStatement)
    (hstab : ∀ m : ℕ, 0 < m → CZCubePosStabOverStatement (Localization.Away (m : ℤ))) :
    CharZeroK2CubeGapPosStatement :=
  czCubePos_charZeroK2CubeGapPos_of_resField_of_cubeStab (czNK2_resField_of_cone h) hstab

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czNK2_gapPos_of_cone_of_cubeStab

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
