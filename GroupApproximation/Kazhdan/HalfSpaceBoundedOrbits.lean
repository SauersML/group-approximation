import GroupApproximation.Kazhdan.DelormeFixedPoint
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Meta.AxiomGuard

/-!
# Property `(T)` bounds the displacement in equivariant half-space systems

This is the analytic half of "property `(T)` implies property FA", in the form
the Guentner--Higson--Weinberger step of `non_mf_groups_exist.tex` (the remark
after `prop:torsion-defect-ring`, tex lines 1146--1150) needs for trees:
a group with property `(T)` acting on a tree has bounded orbits.

A *half-space system* on a `G`-set `X`, indexed by a `G`-set `D`, assigns to
every `d ∈ D` a subset `H_d ⊆ X` with `g • H_d = H_{g • d}`, and any two points
are separated by only finitely many of the `H_d`.  (For a tree, `D` is the set
of oriented edges and `H_{(u,v)}` the vertices closer to `v` than to `u`.)

The separation vector `c(x,y) = 1_{y ∈ H_·} - 1_{x ∈ H_·}` lies in `ℓ²(D)`,
satisfies `c(x,y) + c(y,z) = c(x,z)` and `g · c(x,y) = c(g x, g y)`, and its
squared norm is at least the number of half-spaces separating `x` from `y`.
So `g ↦ c(x₀, g x₀)` is a cocycle for the permutation representation on
`ℓ²(D)`, Delorme's theorem (proved in `Kazhdan/DelormeFixedPoint`) makes it
bounded, and the number of half-spaces separating `x₀` from `g x₀` is bounded
uniformly in `g`.
-/

namespace GroupApproximation

universe u

open scoped ENNReal

/-- An equivariant system of half-spaces on the `G`-set `X`, indexed by the
`G`-set `D`: `g • x ∈ H_{g • d} ↔ x ∈ H_d`, and any two points are separated by
finitely many half-spaces. -/
structure HalfSpaceSystem (G : Type u) [Group G] (X : Type u) [MulAction G X]
    (D : Type u) [MulAction G D] where
  /-- The half-space indexed by `d`. -/
  half : D → Set X
  equivariant : ∀ (g : G) (d : D) (x : X), g • x ∈ half (g • d) ↔ x ∈ half d
  finite_sep : ∀ x y : X, {d : D | ¬ (x ∈ half d ↔ y ∈ half d)}.Finite

namespace HalfSpaceSystem

variable {G : Type u} [Group G] {X : Type u} [MulAction G X] {D : Type u} [MulAction G D]
  (W : HalfSpaceSystem G X D)

/-- The half-spaces separating `x` from `y`, as a finite set. -/
noncomputable def sepFinset (x y : X) : Finset D := (W.finite_sep x y).toFinset

theorem mem_sepFinset {x y : X} {d : D} :
    d ∈ W.sepFinset x y ↔ ¬ (x ∈ W.half d ↔ y ∈ W.half d) :=
  Set.Finite.mem_toFinset _

/-- The indicator `1_{x ∈ H_d}`. -/
noncomputable def ind (x : X) (d : D) : ℝ :=
  Set.indicator (W.half d) (fun _ ↦ (1 : ℝ)) x

theorem ind_eq_of_iff {x y : X} {d : D} (h : x ∈ W.half d ↔ y ∈ W.half d) :
    W.ind x d = W.ind y d := by
  by_cases hx : x ∈ W.half d
  · rw [ind, ind, Set.indicator_of_mem hx, Set.indicator_of_mem (h.mp hx)]
  · rw [ind, ind, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun hy ↦ hx (h.mpr hy))]

theorem abs_ind_sub_ind_of_mem_sepFinset {x y : X} {d : D} (hd : d ∈ W.sepFinset x y) :
    ‖W.ind y d - W.ind x d‖ = 1 := by
  have hsep := (W.mem_sepFinset).mp hd
  by_cases hx : x ∈ W.half d
  · have hy : y ∉ W.half d := fun hy ↦ hsep ⟨fun _ ↦ hy, fun _ ↦ hx⟩
    rw [ind, ind, Set.indicator_of_mem hx, Set.indicator_of_notMem hy]
    norm_num
  · have hy : y ∈ W.half d := by
      by_contra hy
      exact hsep ⟨fun h ↦ absurd h hx, fun h ↦ absurd h hy⟩
    rw [ind, ind, Set.indicator_of_notMem hx, Set.indicator_of_mem hy]
    norm_num

/-- The separation vector `c(x,y) = 1_{y ∈ H_·} - 1_{x ∈ H_·}` in `ℓ²(D)`. -/
noncomputable def sepVec (x y : X) : lp (fun _ : D ↦ ℝ) 2 :=
  ⟨fun d ↦ W.ind y d - W.ind x d, by
    refine memℓp_gen (summable_of_ne_finset_zero (s := W.sepFinset x y) fun d hd ↦ ?_)
    have hiff : x ∈ W.half d ↔ y ∈ W.half d := by
      by_contra h
      exact hd ((W.mem_sepFinset).mpr h)
    rw [W.ind_eq_of_iff hiff, sub_self, norm_zero]
    exact Real.zero_rpow (by norm_num)⟩

@[simp] theorem sepVec_apply (x y : X) (d : D) : W.sepVec x y d = W.ind y d - W.ind x d := rfl

/-- `c(x,y) + c(y,z) = c(x,z)`. -/
theorem sepVec_add (x y z : X) : W.sepVec x y + W.sepVec y z = W.sepVec x z := by
  apply lp.ext
  funext d
  rw [lp.coeFn_add, Pi.add_apply, sepVec_apply, sepVec_apply, sepVec_apply]
  ring

theorem ind_inv_smul (g : G) (x : X) (d : D) : W.ind x (g⁻¹ • d) = W.ind (g • x) d := by
  have h := W.equivariant g (g⁻¹ • d) x
  rw [smul_inv_smul] at h
  by_cases hx : x ∈ W.half (g⁻¹ • d)
  · rw [ind, ind, Set.indicator_of_mem hx, Set.indicator_of_mem (h.mpr hx)]
  · rw [ind, ind, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' ↦ hx (h.mp h'))]

/-- `g · c(x,y) = c(g x, g y)` for the permutation representation on `ℓ²(D)`. -/
theorem permutationRepresentation_sepVec (g : G) (x y : X) :
    KazhdanFiniteGeneration.permutationRepresentation G D g (W.sepVec x y) =
      W.sepVec (g • x) (g • y) := by
  apply lp.ext
  funext d
  rw [KazhdanFiniteGeneration.permutationRepresentation_apply, sepVec_apply, sepVec_apply,
    W.ind_inv_smul, W.ind_inv_smul]

/-- The squared norm of `c(x,y)` is at least the number of separating
half-spaces. -/
theorem card_sepFinset_le_norm_rpow (x y : X) :
    ((W.sepFinset x y).card : ℝ) ≤ ‖W.sepVec x y‖ ^ (2 : ℝ≥0∞).toReal := by
  have h := lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (W.sepVec x y) (W.sepFinset x y)
  have hone : ∀ d ∈ W.sepFinset x y, ‖W.sepVec x y d‖ ^ (2 : ℝ≥0∞).toReal = 1 := by
    intro d hd
    rw [sepVec_apply, W.abs_ind_sub_ind_of_mem_sepFinset hd, Real.one_rpow]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-- The orbit cocycle `g ↦ c(x₀, g x₀)`. -/
theorem isCocycle_orbit (x₀ : X) :
    Delorme.IsCocycle (KazhdanFiniteGeneration.permutationRepresentation G D)
      (fun g ↦ W.sepVec x₀ (g • x₀)) := by
  intro g h
  show W.sepVec x₀ ((g * h) • x₀) =
    W.sepVec x₀ (g • x₀) + KazhdanFiniteGeneration.permutationRepresentation G D g
      (W.sepVec x₀ (h • x₀))
  rw [permutationRepresentation_sepVec, mul_smul, sepVec_add]

/-- **Property `(T)` bounds the separation.**  For a group with property `(T)`
and any base point, the number of half-spaces separating `x₀` from `g x₀` is
bounded uniformly in `g`. -/
theorem exists_card_sepFinset_bound (hT : HasKazhdanPropertyT.{u, u} G) (x₀ : X) :
    ∃ R : ℝ, ∀ g : G, ((W.sepFinset x₀ (g • x₀)).card : ℝ) ≤ R := by
  obtain ⟨ξ, hξ⟩ := Delorme.exists_fixed_point_of_hasKazhdanPropertyT hT
    (KazhdanFiniteGeneration.permutationRepresentation G D) (W.isCocycle_orbit x₀)
  refine ⟨(2 * ‖ξ‖) ^ (2 : ℝ≥0∞).toReal, fun g ↦ ?_⟩
  have hbound : ‖W.sepVec x₀ (g • x₀)‖ ≤ 2 * ‖ξ‖ := by
    have hbg : W.sepVec x₀ (g • x₀) =
        ξ - KazhdanFiniteGeneration.permutationRepresentation G D g ξ := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact hξ g
    rw [hbg]
    calc ‖ξ - KazhdanFiniteGeneration.permutationRepresentation G D g ξ‖
        ≤ ‖ξ‖ + ‖KazhdanFiniteGeneration.permutationRepresentation G D g ξ‖ := norm_sub_le _ _
      _ = 2 * ‖ξ‖ := by rw [LinearIsometryEquiv.norm_map]; ring
  exact (W.card_sepFinset_le_norm_rpow x₀ (g • x₀)).trans
    (Real.rpow_le_rpow (norm_nonneg _) hbound (by norm_num))

end HalfSpaceSystem
end GroupApproximation

#audit_axioms GroupApproximation.HalfSpaceSystem.exists_card_sepFinset_bound
