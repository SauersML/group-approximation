import GroupApproximation.Kazhdan.KazhdanFixedSpace
import GroupApproximation.Kazhdan.HilbertEpsilonOrthogonality
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
# The `1 / sqrt 2` angle bound for a concrete Heisenberg pair

`ClassTwoOrthogonality.epsilonOrthogonal` bounds the angle between the fixed
subspaces of two abelian subgroups whose cross-commutator is central by making
every finite stage a *finite* group and averaging over it.  That average costs
a bounded exponent, so over a torsion-free coefficient ring — the Heisenberg
group on `degreeLE X ℤ n` being the case of interest — it is unavailable.

This file proves the same bound with no exponent, no finiteness and no
commutativity, for any class-two pair whose cross-commutators are generated,
modulo a central subgroup, by *finitely many* commutators of the two
subgroups.  Two finitely generated subgroups always satisfy that, which is
exactly the situation of the Heisenberg group over a finitely generated
coefficient module such as `degreeLE X ℤ n` for a finite alphabet `X`.

The finite average is replaced by two devices.

* **A two-term convex combination.**  If one element `x` of the left subgroup
  makes the correlation `⟪rho x v, v⟫` nonpositive, then
  `2 ⟪u, v⟫ = ⟪u, v + rho x v⟫` and `‖v + rho x v‖ ^ 2 ≤ 2 ‖v‖ ^ 2` already
  give the bound: see `abs_inner_le_of_correlation_nonpos`.  No averaging, no
  finiteness, no exponent.
* **The von Neumann mean ergodic theorem** for the single orthogonal operator
  `rho c`, where `c` is the central commutator, in the form
  `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`.
  Conjugating `x` by powers of `y` multiplies it by powers of `c`, so the
  correlation `⟪rho x v, v⟫` is unchanged along the whole `c`-orbit; it
  therefore equals the correlation of the ergodic mean, which is a `c`-fixed
  vector of the closed invariant subspace `v` is orthogonal to, so it
  vanishes.  This is `inner_translate_eq_zero`, and it replaces the finite
  geometric sum
  `FiniteClassTwoOrthogonality.geomSum_apply_eq_zero_of_fixedSubmodule_bot`.

Splitting off one central commutator at a time then runs as an induction over
a finite list of commutators (`abs_inner_le_of_commutatorList`), whose base
case is exact orthogonality of the two fixed spaces
(`inner_eq_zero_of_commutators_mem`).  The statement for a finitely generated
pair is `epsilonOrthogonal_of_generators`.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u v

namespace HeisenbergAngleBound

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Real-arithmetic helpers -/

/-- Passing from a squared half estimate to the `1 / sqrt 2` estimate. -/
theorem le_inv_sqrt_two_mul_of_sq_le_half {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ (1 / 2 : ℝ) * b ^ 2) :
    a ≤ (Real.sqrt 2)⁻¹ * b := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hinv : 0 ≤ (Real.sqrt 2)⁻¹ := inv_nonneg.mpr hsqrt.le
  have hsquare : ((Real.sqrt 2)⁻¹ * b) ^ 2 = (1 / 2 : ℝ) * b ^ 2 := by
    have hsqrtSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    field_simp
    rw [hsqrtSq]
    ring
  have hsq : a ^ 2 ≤ ((Real.sqrt 2)⁻¹ * b) ^ 2 := by rwa [hsquare]
  exact (sq_le_sq₀ ha (mul_nonneg hinv hb)).mp hsq

/-- The two-dimensional Cauchy--Schwarz inequality, in the shape needed to
recombine an orthogonal splitting by Pythagoras. -/
theorem mul_add_mul_le_of_pythagoras {p q r s t w : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ht0 : 0 ≤ t) (hw0 : 0 ≤ w)
    (ht : t ^ 2 = p ^ 2 + q ^ 2) (hw : w ^ 2 = r ^ 2 + s ^ 2) :
    p * r + q * s ≤ t * w := by
  have h1 : (p * r + q * s) ^ 2 ≤ (t * w) ^ 2 := by
    nlinarith [sq_nonneg (p * s - q * r), ht, hw]
  exact (sq_le_sq₀ (add_nonneg (mul_nonneg hp hr) (mul_nonneg hq hs))
    (mul_nonneg ht0 hw0)).mp h1

/-! ### The two-term convex combination -/

/-- If a single group element moves `v` to a vector with nonpositive
correlation, the `1 / sqrt 2` angle bound holds outright.  This is the
exponent-free replacement for the finite orbit average: it uses one group
element instead of a whole finite orbit. -/
theorem abs_inner_le_of_correlation_nonpos
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {x : G} {u v : E}
    (hu : rho x u = u)
    (hcorr : (inner ℝ (rho x v) v : ℝ) ≤ 0) :
    |inner ℝ u v| ≤ (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖ := by
  have hshift : (inner ℝ u (rho x v) : ℝ) = inner ℝ u v := by
    have h := (rho x).inner_map_map u v
    rw [hu] at h
    exact h
  have hsum : (inner ℝ u (v + rho x v) : ℝ) = 2 * inner ℝ u v := by
    rw [inner_add_right, hshift]
    ring
  have hnormeq : ‖rho x v‖ = ‖v‖ := (rho x).norm_map v
  have hsymm : (inner ℝ v (rho x v) : ℝ) = inner ℝ (rho x v) v :=
    real_inner_comm (rho x v) v
  have hs2 : ‖v + rho x v‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, hnormeq, hsymm]
    linarith
  have hCS : |(2 : ℝ) * inner ℝ u v| ≤ ‖u‖ * ‖v + rho x v‖ := by
    rw [← hsum]
    exact abs_real_inner_le_norm u (v + rho x v)
  have habs2 : |(2 : ℝ) * inner ℝ u v| = |inner ℝ u v| * 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [habs2] at hCS
  have hprod : (|inner ℝ u v| * 2) * (|inner ℝ u v| * 2) ≤
      (‖u‖ * ‖v + rho x v‖) * (‖u‖ * ‖v + rho x v‖) :=
    mul_le_mul hCS hCS (by positivity) (by positivity)
  have hmul : ‖u‖ ^ 2 * ‖v + rho x v‖ ^ 2 ≤ ‖u‖ ^ 2 * (2 * ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hs2 (sq_nonneg ‖u‖)
  have hkey : |inner ℝ u v| ^ 2 ≤ (1 / 2 : ℝ) * (‖u‖ * ‖v‖) ^ 2 := by
    nlinarith [hprod, hmul]
  have hfinal := le_inv_sqrt_two_mul_of_sq_le_half
    (abs_nonneg (inner ℝ u v : ℝ)) (by positivity : (0 : ℝ) ≤ ‖u‖ * ‖v‖) hkey
  calc
    |inner ℝ u v| ≤ (Real.sqrt 2)⁻¹ * (‖u‖ * ‖v‖) := hfinal
    _ = (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖ := by ring

/-! ### Invariant subspaces and their orthogonal projections -/

/-- An element whose inverse preserves a subspace preserves its orthogonal
complement. -/
theorem map_mem_orthogonal (rho : G →* (E ≃ₗᵢ[ℝ] E)) {Q : Submodule ℝ E} {g : G}
    (hginv : ∀ z ∈ Q, rho g⁻¹ z ∈ Q) {w : E} (hw : w ∈ Qᗮ) :
    rho g w ∈ Qᗮ := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hz' : rho g⁻¹ z ∈ Q := hginv z hz
  have hcancel : rho g⁻¹ (rho g w) = w := by simp
  calc
    inner ℝ z (rho g w) = inner ℝ (rho g⁻¹ z) (rho g⁻¹ (rho g w)) := by
      rw [(rho g⁻¹).inner_map_map]
    _ = inner ℝ (rho g⁻¹ z) w := by rw [hcancel]
    _ = 0 := Submodule.inner_right_of_mem_orthogonal hz' hw

/-- Orthogonal projection onto an invariant subspace commutes with the
action. -/
theorem starProjection_equivariant (rho : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Submodule ℝ E)
    [Q.HasOrthogonalProjection] {g : G}
    (hg : ∀ z ∈ Q, rho g z ∈ Q) (hginv : ∀ z ∈ Q, rho g⁻¹ z ∈ Q) (z : E) :
    Q.starProjection (rho g z) = rho g (Q.starProjection z) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hg _ (Q.starProjection_apply_mem z)
  · have h : rho g z - rho g (Q.starProjection z) = rho g (z - Q.starProjection z) := by
      rw [map_sub]
    rw [h]
    exact map_mem_orthogonal rho hginv (Q.sub_starProjection_mem_orthogonal z)

/-- The orthogonal projection onto an invariant subspace carries fixed vectors
to fixed vectors. -/
theorem starProjection_mem_fixedSubspace (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (Q : Submodule ℝ E) [Q.HasOrthogonalProjection]
    (hQ : ∀ g : G, ∀ z ∈ Q, rho g z ∈ Q) (K : Subgroup G) {z : E}
    (hz : z ∈ KazhdanFixedSpace.fixedSubspace rho K) :
    Q.starProjection z ∈ KazhdanFixedSpace.fixedSubspace rho K := by
  rw [KazhdanFixedSpace.mem_fixedSubspace_iff] at hz ⊢
  intro h hh
  rw [← starProjection_equivariant rho Q (hQ h) (hQ h⁻¹) z, hz h hh]

/-- The fixed subspace of a central subgroup is invariant under the whole
group. -/
theorem central_fixedSubspace_invariant (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (N : Subgroup G) (hN : N ≤ Subgroup.center G) (g : G) {z : E}
    (hz : z ∈ KazhdanFixedSpace.fixedSubspace rho N) :
    rho g z ∈ KazhdanFixedSpace.fixedSubspace rho N := by
  rw [KazhdanFixedSpace.mem_fixedSubspace_iff] at hz ⊢
  intro h hh
  have hcomm : h * g = g * h := (Subgroup.mem_center_iff.mp (hN hh) g).symm
  calc
    rho h (rho g z) = rho (h * g) z := by simp [map_mul]
    _ = rho (g * h) z := by rw [hcomm]
    _ = rho g (rho h z) := by simp [map_mul]
    _ = rho g z := by rw [hz h hh]

/-! ### The represented central element as a contraction -/

/-- A represented group element, viewed as a norm-one continuous linear map.
This is the form required by the mean ergodic theorem. -/
noncomputable def repOperator (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) : E →L[ℝ] E :=
  (rho c).toLinearIsometry.toContinuousLinearMap

@[simp] theorem repOperator_apply (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) (z : E) :
    repOperator rho c z = rho c z := rfl

theorem norm_repOperator_le (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) :
    ‖repOperator rho c‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

theorem repOperator_iterate (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) :
    ∀ (k : ℕ) (z : E), (repOperator rho c)^[k] z = rho (c ^ k) z := by
  intro k
  induction k with
  | zero => intro z; simp
  | succ i ih =>
      intro z
      rw [Function.iterate_succ_apply, ih, pow_succ]
      simp [map_mul]

/-! ### The vanishing correlation, by the mean ergodic theorem -/

/-- **The exponent-free vanishing lemma.**  Let `⁅y, x⁆` be central, let `N`
be a central subgroup, and let `v` be fixed by `Y` and by `N` but orthogonal
to the part of the `N`-fixed subspace on which `⁅y, x⁆` also acts trivially.
Then the correlation `⟪rho x v, v⟫` vanishes.

Conjugating `x` by `y ^ k` multiplies it by `⁅y, x⁆ ^ k`, so the correlation
is unchanged along the whole orbit of the central commutator; the von Neumann
mean ergodic theorem identifies the Cesàro mean of that orbit with a fixed
vector of `rho ⁅y, x⁆`, which stays inside the closed invariant subspace
`fixedSubspace rho N` and is therefore orthogonal to `v`. -/
theorem inner_translate_eq_zero [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (Y N : Subgroup G)
    (hN : N ≤ Subgroup.center G)
    {y x : G} (hy : y ∈ Y) (hc : ⁅y, x⁆ ∈ Subgroup.center G)
    {v : E}
    (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y)
    (hvN : v ∈ KazhdanFixedSpace.fixedSubspace rho N)
    (hvperp : v ∈ (KazhdanFixedSpace.fixedSubspace rho
      (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G)))ᗮ) :
    (inner ℝ (rho x v) v : ℝ) = 0 := by
  have hcy : Commute ⁅y, x⁆ y := (Subgroup.mem_center_iff.mp hc y).symm
  -- conjugating `x` by `y ^ k` multiplies it by the `k`-th power of the commutator
  have hconjPow : ∀ k : ℕ, y ^ k * x * (y ^ k)⁻¹ = ⁅y, x⁆ ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ i ih =>
        calc
          y ^ (i + 1) * x * (y ^ (i + 1))⁻¹ =
              y * (y ^ i * x * (y ^ i)⁻¹) * y⁻¹ := by group
          _ = y * (⁅y, x⁆ ^ i * x) * y⁻¹ := by rw [ih]
          _ = ⁅y, x⁆ ^ i * (y * x * y⁻¹) := by
              calc
                y * (⁅y, x⁆ ^ i * x) * y⁻¹ = (y * ⁅y, x⁆ ^ i) * x * y⁻¹ := by
                  simp only [mul_assoc]
                _ = (⁅y, x⁆ ^ i * y) * x * y⁻¹ := by
                  rw [(hcy.symm.pow_right i).eq]
                _ = ⁅y, x⁆ ^ i * (y * x * y⁻¹) := by simp only [mul_assoc]
          _ = ⁅y, x⁆ ^ i * (⁅y, x⁆ * x) := by
              rw [← conj_eq_commutatorElement_mul]
              rfl
          _ = ⁅y, x⁆ ^ (i + 1) * x := by rw [pow_succ]; group
  -- the correlation is unchanged along the orbit of the central commutator
  have hinner : ∀ k : ℕ,
      (inner ℝ (rho (⁅y, x⁆ ^ k) (rho x v)) v : ℝ) = inner ℝ (rho x v) v := by
    intro k
    have hyPow : y ^ k ∈ Y := Y.pow_mem hy k
    have hyfix : rho (y ^ k) v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY _ hyPow
    have hyinvfix : rho (y ^ k)⁻¹ v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY _ (Y.inv_mem hyPow)
    calc
      (inner ℝ (rho (⁅y, x⁆ ^ k) (rho x v)) v : ℝ)
          = inner ℝ (rho (⁅y, x⁆ ^ k * x) v) v := by
            simp only [map_mul]
            rfl
      _ = inner ℝ (rho (y ^ k * x * (y ^ k)⁻¹) v) v := by rw [hconjPow k]
      _ = inner ℝ (rho (y ^ k) (rho x (rho (y ^ k)⁻¹ v))) v := by
            simp only [map_mul]
            rfl
      _ = inner ℝ (rho (y ^ k) (rho x v)) (rho (y ^ k) v) := by
            rw [hyinvfix, hyfix]
      _ = inner ℝ (rho x v) v := (rho (y ^ k)).inner_map_map _ _
  -- the mean ergodic theorem for the single orthogonal operator `rho ⁅y, x⁆`
  have hlim := (repOperator rho ⁅y, x⁆).tendsto_birkhoffAverage_orthogonalProjection
    (norm_repOperator_le rho ⁅y, x⁆) (rho x v)
  have hrepr : ∀ n : ℕ,
      birkhoffAverage ℝ (repOperator rho ⁅y, x⁆) _root_.id n (rho x v)
        = (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n,
            (repOperator rho ⁅y, x⁆)^[k] (rho x v) := fun _ ↦ rfl
  -- every Birkhoff average stays in the closed invariant subspace `Fix N`
  have hxvN : rho x v ∈ KazhdanFixedSpace.fixedSubspace rho N :=
    central_fixedSubspace_invariant rho N hN x hvN
  have hmemN : ∀ n : ℕ,
      birkhoffAverage ℝ (repOperator rho ⁅y, x⁆) _root_.id n (rho x v)
        ∈ KazhdanFixedSpace.fixedSubspace rho N := by
    intro n
    rw [hrepr n]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro k _
    rw [repOperator_iterate]
    exact central_fixedSubspace_invariant rho N hN _ hxvN
  -- hence so does the limit
  have hlimN :
      (((repOperator rho ⁅y, x⁆).eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto
        (rho x v) : E) ∈ KazhdanFixedSpace.fixedSubspace rho N :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho N).mem_of_tendsto hlim
      (Filter.Eventually.of_forall hmemN)
  -- and the limit is fixed by the central commutator
  have hlimc : rho ⁅y, x⁆
      (((repOperator rho ⁅y, x⁆).eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto
        (rho x v) : E)
      = (((repOperator rho ⁅y, x⁆).eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto
        (rho x v) : E) := by
    have h0 := (((repOperator rho ⁅y, x⁆).eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto
      (rho x v)).2
    -- membership in an `eqLocus` is definitionally the equation it names
    have h1 : repOperator rho ⁅y, x⁆
        (((repOperator rho ⁅y, x⁆).eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto
          (rho x v) : E)
        = (1 : E →L[ℝ] E)
          (((repOperator rho ⁅y, x⁆).eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto
            (rho x v) : E) := h0
    simpa using h1
  -- so the limit lies in the subspace to which `v` is orthogonal
  have hlimW :
      (((repOperator rho ⁅y, x⁆).eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto
        (rho x v) : E) ∈ KazhdanFixedSpace.fixedSubspace rho
        (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G)) := by
    rw [KazhdanFixedSpace.fixedSubspace_sup]
    refine Submodule.mem_inf.mpr ⟨hlimN, ?_⟩
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro h hh
    refine KazhdanFixedSpace.fixed_of_mem_closure rho ({⁅y, x⁆} : Set G) _ ?_ h hh
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hlimc
  -- compare the two limits of the correlation sequence
  have hcont : Filter.Tendsto
      (fun n : ℕ => (inner ℝ
        (birkhoffAverage ℝ (repOperator rho ⁅y, x⁆) _root_.id n (rho x v)) v : ℝ))
      Filter.atTop
      (nhds (inner ℝ
        (((repOperator rho ⁅y, x⁆).eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto
          (rho x v) : E) v)) :=
    hlim.inner tendsto_const_nhds
  have hconstval : ∀ n : ℕ, 1 ≤ n →
      (inner ℝ
        (birkhoffAverage ℝ (repOperator rho ⁅y, x⁆) _root_.id n (rho x v)) v : ℝ)
        = inner ℝ (rho x v) v := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hterm : ∀ k ∈ Finset.range n,
        (inner ℝ ((repOperator rho ⁅y, x⁆)^[k] (rho x v)) v : ℝ)
          = inner ℝ (rho x v) v := by
      intro k _
      rw [repOperator_iterate]
      exact hinner k
    have hsum : ∑ k ∈ Finset.range n,
        (inner ℝ ((repOperator rho ⁅y, x⁆)^[k] (rho x v)) v : ℝ)
          = (n : ℝ) * inner ℝ (rho x v) v := by
      rw [Finset.sum_congr rfl hterm]
      simp
    rw [hrepr n, real_inner_smul_left, sum_inner, hsum]
    field_simp
  have hconstT : Filter.Tendsto
      (fun _ : ℕ => (inner ℝ (rho x v) v : ℝ)) Filter.atTop
      (nhds (inner ℝ (rho x v) v)) := tendsto_const_nhds
  have hF : Filter.Tendsto
      (fun n : ℕ => (inner ℝ
        (birkhoffAverage ℝ (repOperator rho ⁅y, x⁆) _root_.id n (rho x v)) v : ℝ))
      Filter.atTop (nhds (inner ℝ (rho x v) v)) := by
    refine Filter.Tendsto.congr' ?_ hconstT
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (hconstval n hn).symm
  rw [tendsto_nhds_unique hF hcont]
  exact Submodule.inner_right_of_mem_orthogonal hlimW hvperp

/-! ### The degenerate case: exact orthogonality -/

/-- When every cross-commutator lies in a central subgroup `N`, the vectors
fixed by `X` and by `N` are exactly orthogonal to the vectors fixed by `Y`.
This is the base case of the induction: no angle defect at all. -/
theorem inner_eq_zero_of_commutators_mem [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y N : Subgroup G)
    (hgen : X ⊔ Y = ⊤)
    (hN : N ≤ Subgroup.center G)
    (hcomm : ∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ N)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    {u v : E}
    (hu : u ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ N))
    (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    (inner ℝ u v : ℝ) = 0 := by
  letI : CompleteSpace (KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)) :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho (X ⊔ N)).completeSpace_coe
  -- the `X`-and-`N`-fixed subspace is invariant under `Y`
  have hVinv : ∀ g ∈ Y, ∀ z ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ N),
      rho g z ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ N) := by
    intro g hg z hz
    have hzX : z ∈ KazhdanFixedSpace.fixedSubspace rho X :=
      KazhdanFixedSpace.antitone rho le_sup_left hz
    have hzN : z ∈ KazhdanFixedSpace.fixedSubspace rho N :=
      KazhdanFixedSpace.antitone rho le_sup_right hz
    have hgzN : rho g z ∈ KazhdanFixedSpace.fixedSubspace rho N :=
      central_fixedSubspace_invariant rho N hN g hzN
    rw [KazhdanFixedSpace.fixedSubspace_sup]
    refine Submodule.mem_inf.mpr ⟨?_, hgzN⟩
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro w hw
    have hcw : ⁅w, g⁆ ∈ N := by
      have hflip : ⁅w, g⁆ = ⁅g, w⁆⁻¹ := (commutatorElement_inv g w).symm
      rw [hflip]
      exact N.inv_mem (hcomm g hg w hw)
    have hwz : rho w z = z :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho X z).mp hzX w hw
    have hfixN : rho ⁅w, g⁆ (rho g z) = rho g z :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho N (rho g z)).mp hgzN _ hcw
    have hid : w * g = ⁅w, g⁆ * g * w := by
      rw [commutatorElement_def]
      group
    calc
      rho w (rho g z) = rho (w * g) z := by simp [map_mul]
      _ = rho (⁅w, g⁆ * g * w) z := by rw [hid]
      _ = rho ⁅w, g⁆ (rho g (rho w z)) := by
          simp only [map_mul]
          rfl
      _ = rho ⁅w, g⁆ (rho g z) := by rw [hwz]
      _ = rho g z := hfixN
  -- the projection of `v` is fixed by everything, hence zero
  have hPvV : (KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)).starProjection v
      ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ N) :=
    Submodule.starProjection_apply_mem _ v
  have hPvX : (KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)).starProjection v
      ∈ KazhdanFixedSpace.fixedSubspace rho X :=
    KazhdanFixedSpace.antitone rho le_sup_left hPvV
  have hPvY : ∀ g ∈ Y,
      rho g ((KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)).starProjection v)
        = (KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)).starProjection v := by
    intro g hg
    have hvg : rho g v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY g hg
    rw [← starProjection_equivariant rho _ (hVinv g hg) (hVinv g⁻¹ (Y.inv_mem hg)) v,
      hvg]
  have hPvglobal : ∀ g : G,
      rho g ((KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)).starProjection v)
        = (KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)).starProjection v := by
    intro g
    have hseed : ∀ s ∈ (X : Set G) ∪ (Y : Set G),
        rho s ((KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)).starProjection v)
          = (KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)).starProjection v := by
      intro s hs
      rcases hs with hs | hs
      · exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho X _).mp hPvX s hs
      · exact hPvY s hs
    refine KazhdanFixedSpace.fixed_of_mem_closure rho ((X : Set G) ∪ (Y : Set G))
      _ hseed g ?_
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, hgen]
    exact Subgroup.mem_top g
  have hPvzero : (KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)).starProjection v = 0 :=
    hno _ hPvglobal
  have hvsplit : v - (KazhdanFixedSpace.fixedSubspace rho (X ⊔ N)).starProjection v
      ∈ (KazhdanFixedSpace.fixedSubspace rho (X ⊔ N))ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal v
  rw [hPvzero, sub_zero] at hvsplit
  exact Submodule.inner_right_of_mem_orthogonal hu hvsplit

/-! ### Splitting along an invariant subspace -/

/-- One induction step, in purely Hilbert-space terms.  `Q` is an invariant
subspace carrying an orthogonal projection; on `Q` the bound is assumed, and
on its orthogonal complement the vanishing correlation makes the two-term
convex combination apply.  Pythagoras and the two-dimensional Cauchy--Schwarz
inequality recombine the two contributions. -/
theorem abs_inner_le_of_invariant_split
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X : Subgroup G) {x : G} (hxX : x ∈ X)
    (Q : Submodule ℝ E) [Q.HasOrthogonalProjection]
    (hQ : ∀ g : G, ∀ z ∈ Q, rho g z ∈ Q)
    {u v : E}
    (huX : u ∈ KazhdanFixedSpace.fixedSubspace rho X)
    (hrec : |inner ℝ (Q.starProjection u) (Q.starProjection v)| ≤
      (Real.sqrt 2)⁻¹ * ‖Q.starProjection u‖ * ‖Q.starProjection v‖)
    (hperp : (inner ℝ (rho x (v - Q.starProjection v)) (v - Q.starProjection v) : ℝ)
      = 0) :
    |inner ℝ u v| ≤ (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖ := by
  have hPuQ : Q.starProjection u ∈ Q := Q.starProjection_apply_mem u
  have hPvQ : Q.starProjection v ∈ Q := Q.starProjection_apply_mem v
  have huR : u - Q.starProjection u ∈ Qᗮ := Q.sub_starProjection_mem_orthogonal u
  have hvR : v - Q.starProjection v ∈ Qᗮ := Q.sub_starProjection_mem_orthogonal v
  have hsplitu : Q.starProjection u + (u - Q.starProjection u) = u := by abel
  have hsplitv : Q.starProjection v + (v - Q.starProjection v) = v := by abel
  -- the complementary component of `u` is still `X`-fixed
  have hPuX : Q.starProjection u ∈ KazhdanFixedSpace.fixedSubspace rho X :=
    starProjection_mem_fixedSubspace rho Q hQ X huX
  have huRX : rho x (u - Q.starProjection u) = u - Q.starProjection u := by
    rw [map_sub, (KazhdanFixedSpace.mem_fixedSubspace_iff rho X u).mp huX x hxX,
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho X _).mp hPuX x hxX]
  have hcomp := abs_inner_le_of_correlation_nonpos rho huRX (le_of_eq hperp)
  -- the cross terms vanish
  have hcross1 : (inner ℝ (Q.starProjection u) (v - Q.starProjection v) : ℝ) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hPuQ hvR
  have hcross2 : (inner ℝ (u - Q.starProjection u) (Q.starProjection v) : ℝ) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hPvQ huR
  have hinner : (inner ℝ u v : ℝ) =
      inner ℝ (Q.starProjection u) (Q.starProjection v)
        + inner ℝ (u - Q.starProjection u) (v - Q.starProjection v) := by
    have h1 : (inner ℝ (Q.starProjection u + (u - Q.starProjection u))
        (Q.starProjection v + (v - Q.starProjection v)) : ℝ)
        = inner ℝ (Q.starProjection u) (Q.starProjection v)
          + inner ℝ (Q.starProjection u) (v - Q.starProjection v)
          + (inner ℝ (u - Q.starProjection u) (Q.starProjection v)
            + inner ℝ (u - Q.starProjection u) (v - Q.starProjection v)) := by
      rw [inner_add_left, inner_add_right, inner_add_right]
    rw [hsplitu, hsplitv] at h1
    rw [h1, hcross1, hcross2]
    ring
  -- Pythagoras on both vectors
  have hpyth : ∀ a b : E, (inner ℝ a b : ℝ) = 0 →
      ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    intro a b hab
    rw [norm_add_sq_real, hab]
    ring
  have hnu : ‖u‖ ^ 2 = ‖Q.starProjection u‖ ^ 2 + ‖u - Q.starProjection u‖ ^ 2 := by
    have h := hpyth (Q.starProjection u) (u - Q.starProjection u)
      (Submodule.inner_right_of_mem_orthogonal hPuQ huR)
    rw [hsplitu] at h
    exact h
  have hnv : ‖v‖ ^ 2 = ‖Q.starProjection v‖ ^ 2 + ‖v - Q.starProjection v‖ ^ 2 := by
    have h := hpyth (Q.starProjection v) (v - Q.starProjection v)
      (Submodule.inner_right_of_mem_orthogonal hPvQ hvR)
    rw [hsplitv] at h
    exact h
  have hprod := mul_add_mul_le_of_pythagoras
    (norm_nonneg (Q.starProjection u)) (norm_nonneg (u - Q.starProjection u))
    (norm_nonneg (Q.starProjection v)) (norm_nonneg (v - Q.starProjection v))
    (norm_nonneg u) (norm_nonneg v) hnu hnv
  have hinv : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
  calc
    |inner ℝ u v|
        ≤ |inner ℝ (Q.starProjection u) (Q.starProjection v)|
          + |inner ℝ (u - Q.starProjection u) (v - Q.starProjection v)| := by
          rw [hinner]
          exact abs_add_le _ _
    _ ≤ (Real.sqrt 2)⁻¹ * ‖Q.starProjection u‖ * ‖Q.starProjection v‖
          + (Real.sqrt 2)⁻¹ * ‖u - Q.starProjection u‖
            * ‖v - Q.starProjection v‖ := add_le_add hrec hcomp
    _ = (Real.sqrt 2)⁻¹ * (‖Q.starProjection u‖ * ‖Q.starProjection v‖
          + ‖u - Q.starProjection u‖ * ‖v - Q.starProjection v‖) := by ring
    _ ≤ (Real.sqrt 2)⁻¹ * (‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left hprod hinv
    _ = (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖ := by ring

/-- Splitting off one central commutator `⁅y, x⁆`: on the subspace where it
acts trivially the bound is inherited from the enlarged central subgroup, and
on the orthogonal complement the vanishing lemma feeds the two-term convex
combination. -/
theorem abs_inner_le_step [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y N : Subgroup G) {y x : G}
    (hN : N ≤ Subgroup.center G)
    (hyY : y ∈ Y) (hxX : x ∈ X)
    (hc : ⁅y, x⁆ ∈ Subgroup.center G)
    (hrec : ∀ a ∈ KazhdanFixedSpace.fixedSubspace rho
        (X ⊔ (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G))),
      ∀ b ∈ KazhdanFixedSpace.fixedSubspace rho
        (Y ⊔ (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G))),
        |inner ℝ a b| ≤ (Real.sqrt 2)⁻¹ * ‖a‖ * ‖b‖)
    {u v : E}
    (hu : u ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ N))
    (hv : v ∈ KazhdanFixedSpace.fixedSubspace rho (Y ⊔ N)) :
    |inner ℝ u v| ≤ (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖ := by
  have hNc : Subgroup.closure ({⁅y, x⁆} : Set G) ≤ Subgroup.center G :=
    (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hc)
  have hN' : N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G) ≤ Subgroup.center G :=
    sup_le hN hNc
  letI : CompleteSpace (KazhdanFixedSpace.fixedSubspace rho
      (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G))) :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho
      (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G))).completeSpace_coe
  have hQ : ∀ g : G, ∀ z ∈ KazhdanFixedSpace.fixedSubspace rho
      (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G)),
      rho g z ∈ KazhdanFixedSpace.fixedSubspace rho
        (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G)) :=
    fun g z hz ↦ central_fixedSubspace_invariant rho
      (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G)) hN' g hz
  have huX : u ∈ KazhdanFixedSpace.fixedSubspace rho X :=
    KazhdanFixedSpace.antitone rho le_sup_left hu
  have hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y :=
    KazhdanFixedSpace.antitone rho le_sup_left hv
  have hvN : v ∈ KazhdanFixedSpace.fixedSubspace rho N :=
    KazhdanFixedSpace.antitone rho le_sup_right hv
  refine abs_inner_le_of_invariant_split rho X hxX
    (KazhdanFixedSpace.fixedSubspace rho (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G)))
    hQ huX ?_ ?_
  · -- on the fixed part of the commutator, the enlarged bound applies
    refine hrec _ ?_ _ ?_
    · rw [KazhdanFixedSpace.fixedSubspace_sup]
      exact Submodule.mem_inf.mpr
        ⟨starProjection_mem_fixedSubspace rho _ hQ X huX,
          Submodule.starProjection_apply_mem _ u⟩
    · rw [KazhdanFixedSpace.fixedSubspace_sup]
      exact Submodule.mem_inf.mpr
        ⟨starProjection_mem_fixedSubspace rho _ hQ Y hvY,
          Submodule.starProjection_apply_mem _ v⟩
  · -- on the complement the correlation vanishes
    have hvYc : v - (KazhdanFixedSpace.fixedSubspace rho
        (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G))).starProjection v
        ∈ KazhdanFixedSpace.fixedSubspace rho Y :=
      Submodule.sub_mem _ hvY (starProjection_mem_fixedSubspace rho _ hQ Y hvY)
    have hvNc : v - (KazhdanFixedSpace.fixedSubspace rho
        (N ⊔ Subgroup.closure ({⁅y, x⁆} : Set G))).starProjection v
        ∈ KazhdanFixedSpace.fixedSubspace rho N := by
      refine Submodule.sub_mem _ hvN ?_
      exact KazhdanFixedSpace.antitone rho le_sup_left
        (Submodule.starProjection_apply_mem _ v)
    exact inner_translate_eq_zero rho Y N hN hyY hc hvYc hvNc
      (Submodule.sub_starProjection_mem_orthogonal v)

/-! ### The induction over a finite list of central commutators -/

/-- **Exponent-free class-two orthogonality, list form.**  `L` lists finitely
many pairs whose commutators, together with the central subgroup `N`,
generate every commutator `⁅y, x⁆`.  The induction splits off one list entry
at a time: on the orthogonal complement of the fixed space of that entry the
two-term convex combination gives the bound outright, and on the fixed space
itself the entry joins `N` and the list shortens.  When the list is empty all
commutators lie in `N` and the two fixed spaces are exactly orthogonal.

No bounded exponent, no finiteness and no commutativity of `X` or `Y` appears
anywhere. -/
theorem abs_inner_le_of_commutatorList [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G)
    (hgen : X ⊔ Y = ⊤)
    (hcentral : ⁅Y, X⁆ ≤ Subgroup.center G)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho) :
    ∀ L : List (G × G), (∀ p ∈ L, p.1 ∈ Y ∧ p.2 ∈ X) →
      ∀ N : Subgroup G, N ≤ Subgroup.center G →
        (∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈
          Subgroup.closure ({g : G | ∃ p ∈ L, ⁅p.1, p.2⁆ = g} ∪ (N : Set G))) →
        ∀ u ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ N),
        ∀ v ∈ KazhdanFixedSpace.fixedSubspace rho (Y ⊔ N),
          |inner ℝ u v| ≤ (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖ := by
  intro L
  induction L with
  | nil =>
      intro _hL N hN hclos u hu v hv
      have hcommN : ∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ N := by
        intro y hy x hx
        have h := hclos y hy x hx
        have hset : {g : G | ∃ p ∈ ([] : List (G × G)), ⁅p.1, p.2⁆ = g}
            = (∅ : Set G) := by
          ext g
          simp
        rw [hset, Set.empty_union, Subgroup.closure_eq] at h
        exact h
      have h0 : (inner ℝ u v : ℝ) = 0 :=
        inner_eq_zero_of_commutators_mem rho X Y N hgen hN hcommN hno hu
          (KazhdanFixedSpace.antitone rho le_sup_left hv)
      rw [h0, abs_zero]
      positivity
  | cons p L ih =>
      intro hL N hN hclos u hu v hv
      have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
      have hcen : ⁅p.1, p.2⁆ ∈ Subgroup.center G :=
        hcentral (Subgroup.commutator_mem_commutator hp.1 hp.2)
      have hNc : Subgroup.closure ({⁅p.1, p.2⁆} : Set G) ≤ Subgroup.center G :=
        (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hcen)
      have hN' : N ⊔ Subgroup.closure ({⁅p.1, p.2⁆} : Set G) ≤ Subgroup.center G :=
        sup_le hN hNc
      have hsub : {g : G | ∃ q ∈ p :: L, ⁅q.1, q.2⁆ = g} ∪ (N : Set G) ⊆
          {g : G | ∃ q ∈ L, ⁅q.1, q.2⁆ = g}
            ∪ ((N ⊔ Subgroup.closure ({⁅p.1, p.2⁆} : Set G) : Subgroup G) : Set G) := by
        intro g hg
        rcases hg with hg | hg
        · obtain ⟨q, hq, hqg⟩ := hg
          rcases List.mem_cons.mp hq with hq' | hq'
          · refine Or.inr ?_
            have hgp : g = ⁅p.1, p.2⁆ := by rw [← hqg, hq']
            rw [hgp]
            exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
          · exact Or.inl ⟨q, hq', hqg⟩
        · exact Or.inr (Subgroup.mem_sup_left hg)
      have hclos' : ∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈
          Subgroup.closure ({g : G | ∃ q ∈ L, ⁅q.1, q.2⁆ = g}
            ∪ ((N ⊔ Subgroup.closure ({⁅p.1, p.2⁆} : Set G) : Subgroup G) : Set G)) :=
        fun y hy x hx ↦ Subgroup.closure_mono hsub (hclos y hy x hx)
      have hLtail : ∀ q ∈ L, q.1 ∈ Y ∧ q.2 ∈ X :=
        fun q hq ↦ hL q (List.mem_cons.mpr (Or.inr hq))
      exact abs_inner_le_step rho X Y N hN hp.1 hp.2 hcen
        (ih hLtail (N ⊔ Subgroup.closure ({⁅p.1, p.2⁆} : Set G)) hN' hclos') hu hv

/-! ### Central commutator calculus -/

theorem commutatorElement_mul_right_of_central {a b c : G}
    (hc : ⁅a, c⁆ ∈ Subgroup.center G) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h : b * ⁅a, c⁆ = ⁅a, c⁆ * b := Subgroup.mem_center_iff.mp hc b
  calc
    ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆) * b⁻¹ := by
      simp only [mul_assoc]
    _ = ⁅a, b⁆ * (⁅a, c⁆ * b) * b⁻¹ := by rw [h]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by group

theorem commutatorElement_mul_left_of_central {a b c : G}
    (hbc : ⁅b, c⁆ ∈ Subgroup.center G) : ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h : a * ⁅b, c⁆ = ⁅b, c⁆ * a := Subgroup.mem_center_iff.mp hbc a
  calc
    a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ = ⁅b, c⁆ * a * a⁻¹ * ⁅a, c⁆ := by rw [h]
    _ = ⁅b, c⁆ * ⁅a, c⁆ := by group

theorem commutatorElement_inv_left_of_central {a b : G}
    (hab : ⁅a, b⁆ ∈ Subgroup.center G) : ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
  have hba : ⁅b, a⁆ = ⁅a, b⁆⁻¹ := (commutatorElement_inv a b).symm
  have hcen : ⁅b, a⁆ ∈ Subgroup.center G := by
    rw [hba]
    exact (Subgroup.center G).inv_mem hab
  rw [commutatorElement_inv_left]
  have h : a⁻¹ * ⁅b, a⁆ = ⁅b, a⁆ * a⁻¹ := Subgroup.mem_center_iff.mp hcen a⁻¹
  calc
    a⁻¹ * ⁅b, a⁆ * a = ⁅b, a⁆ * a⁻¹ * a := by rw [h]
    _ = ⁅b, a⁆ := by group
    _ = ⁅a, b⁆⁻¹ := hba

theorem commutatorElement_inv_right_of_central {a b : G}
    (hab : ⁅a, b⁆ ∈ Subgroup.center G) : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  have hba : ⁅b, a⁆ = ⁅a, b⁆⁻¹ := (commutatorElement_inv a b).symm
  have hcen : ⁅b, a⁆ ∈ Subgroup.center G := by
    rw [hba]
    exact (Subgroup.center G).inv_mem hab
  rw [commutatorElement_inv_right]
  have h : b⁻¹ * ⁅b, a⁆ = ⁅b, a⁆ * b⁻¹ := Subgroup.mem_center_iff.mp hcen b⁻¹
  calc
    b⁻¹ * ⁅b, a⁆ * b = ⁅b, a⁆ * b⁻¹ * b := by rw [h]
    _ = ⁅b, a⁆ := by group
    _ = ⁅a, b⁆⁻¹ := hba

/-- When all commutators `⁅Y, X⁆` are central the commutator map is
bimultiplicative, so every `⁅y, x⁆` already lies in any subgroup containing
the commutators of chosen generating sets.  This is what supplies the finite
list consumed by `abs_inner_le_of_commutatorList`. -/
theorem commutatorElement_mem_of_generators (X Y : Subgroup G) (S T : Set G)
    (C : Subgroup G)
    (hX : Subgroup.closure S = X) (hY : Subgroup.closure T = Y)
    (hcentral : ⁅Y, X⁆ ≤ Subgroup.center G)
    (hC : ∀ t ∈ T, ∀ s ∈ S, ⁅t, s⁆ ∈ C) :
    ∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ C := by
  have hcen : ∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ Subgroup.center G :=
    fun y hy x hx ↦ hcentral (Subgroup.commutator_mem_commutator hy hx)
  have step : ∀ s ∈ S, ∀ y ∈ Y, ⁅y, s⁆ ∈ C := by
    intro s hs
    have hsX : s ∈ X := by
      rw [← hX]
      exact Subgroup.subset_closure hs
    have key : ∀ z ∈ Subgroup.closure T, z ∈ Y ∧ ⁅z, s⁆ ∈ C := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem t ht =>
          refine ⟨?_, hC t ht s hs⟩
          rw [← hY]
          exact Subgroup.subset_closure ht
      | one =>
          refine ⟨Y.one_mem, ?_⟩
          rw [commutatorElement_one_left]
          exact C.one_mem
      | mul a b _ _ iha ihb =>
          refine ⟨Y.mul_mem iha.1 ihb.1, ?_⟩
          rw [commutatorElement_mul_left_of_central (hcen b ihb.1 s hsX)]
          exact C.mul_mem ihb.2 iha.2
      | inv a _ iha =>
          refine ⟨Y.inv_mem iha.1, ?_⟩
          rw [commutatorElement_inv_left_of_central (hcen a iha.1 s hsX)]
          exact C.inv_mem iha.2
    intro y hy
    refine (key y ?_).2
    rw [hY]
    exact hy
  intro y hy x hx
  rw [← hX] at hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact step s hs y hy
  | one =>
      rw [commutatorElement_one_right]
      exact C.one_mem
  | mul a b _ hb iha ihb =>
      have hbX : b ∈ X := by
        rw [← hX]
        exact hb
      rw [commutatorElement_mul_right_of_central (hcen y hy b hbX)]
      exact C.mul_mem iha ihb
  | inv a ha iha =>
      have haX : a ∈ X := by
        rw [← hX]
        exact ha
      rw [commutatorElement_inv_right_of_central (hcen y hy a haX)]
      exact C.inv_mem iha

/-! ### The angle bound for a finitely generated class-two pair -/

/-- **The `1 / sqrt 2` angle bound for a Heisenberg pair.**  Two finitely
generated subgroups `X` and `Y` generate `G` and their cross-commutators are
central.  Then in every orthogonal representation without nonzero invariant
vectors the two fixed subspaces make an angle of at least `π / 4`.

No bounded exponent, no finiteness of `G` and no commutativity of `X` or `Y`
is required.  The Heisenberg group on a finitely generated coefficient module
— `degreeLE X ℤ n` for a finite alphabet `X` is the case of interest — is
exactly of this shape, with `X` and `Y` the two lower root subgroups and
`⁅Y, X⁆` the central upper root subgroup. -/
theorem epsilonOrthogonal_of_generators [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G) (S T : Finset G)
    (hX : Subgroup.closure (S : Set G) = X)
    (hY : Subgroup.closure (T : Set G) = Y)
    (hgen : X ⊔ Y = ⊤)
    (hcentral : ⁅Y, X⁆ ≤ Subgroup.center G)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho) :
    HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho X)
      (KazhdanFixedSpace.fixedSubspace rho Y)
      (Real.sqrt 2)⁻¹ := by
  intro u hu v hv
  have hLmem : ∀ q ∈ (T ×ˢ S).toList, q.1 ∈ Y ∧ q.2 ∈ X := by
    intro q hq
    rw [Finset.mem_toList, Finset.mem_product] at hq
    refine ⟨?_, ?_⟩
    · rw [← hY]
      exact Subgroup.subset_closure (Finset.mem_coe.mpr hq.1)
    · rw [← hX]
      exact Subgroup.subset_closure (Finset.mem_coe.mpr hq.2)
  have hC : ∀ t ∈ (T : Set G), ∀ s ∈ (S : Set G),
      ⁅t, s⁆ ∈ Subgroup.closure
        ({g : G | ∃ q ∈ (T ×ˢ S).toList, ⁅q.1, q.2⁆ = g}
          ∪ ((⊥ : Subgroup G) : Set G)) := by
    intro t ht s hs
    refine Subgroup.subset_closure (Or.inl ⟨(t, s), ?_, rfl⟩)
    rw [Finset.mem_toList, Finset.mem_product]
    exact ⟨Finset.mem_coe.mp ht, Finset.mem_coe.mp hs⟩
  have hclos := commutatorElement_mem_of_generators X Y (S : Set G) (T : Set G)
    (Subgroup.closure
      ({g : G | ∃ q ∈ (T ×ˢ S).toList, ⁅q.1, q.2⁆ = g}
        ∪ ((⊥ : Subgroup G) : Set G)))
    hX hY hcentral hC
  have hbotX : KazhdanFixedSpace.fixedSubspace rho (X ⊔ ⊥)
      = KazhdanFixedSpace.fixedSubspace rho X := by rw [sup_bot_eq]
  have hbotY : KazhdanFixedSpace.fixedSubspace rho (Y ⊔ ⊥)
      = KazhdanFixedSpace.fixedSubspace rho Y := by rw [sup_bot_eq]
  have hu' : u ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ ⊥) := by
    rw [hbotX]
    exact hu
  have hv' : v ∈ KazhdanFixedSpace.fixedSubspace rho (Y ⊔ ⊥) := by
    rw [hbotY]
    exact hv
  exact abs_inner_le_of_commutatorList rho X Y hgen hcentral hno
    ((T ×ˢ S).toList) hLmem ⊥ bot_le hclos u hu' v hv'

end HeisenbergAngleBound
end GroupApproximation
