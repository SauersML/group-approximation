import GroupApproximation.PropertyT.ThreeVertexDuality
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Closures and projected angles for the three-subgroup criterion

Hilbert-space lemmas feeding the proof of Ershov--Jaikin-Zapirain Proposition 3.2 (*Property (T)
for noncommutative universal lattices*, Invent. Math. 179 (2010)):

* `epsilonOrthogonal_topologicalClosure`: `ε`-orthogonality passes to closures;
* `mem_topologicalClosure_of_orthogonal_inf`: inside a closed subspace `V₀ ⊇ A`, a vector
  orthogonal to `V₀ ⊓ Aᗮ` lies in the closure of `A` (the complement of `V₀ ⊓ Aᗮ` taken in `V₀`);
* `eq_zero_of_mem_topologicalClosure`: an `ε`-orthogonal pair with `ε < 1` has closures meeting in
  zero;
* `abs_inner_le_of_projected_angle`: EJZ (3.3).  If the projections to `Cᗮ` of `A` and of `B` are
  `ε`-orthogonal, then a vector orthogonal to `A` and `C` and a vector orthogonal to `B` and `C`
  lying in the closure of `A + B + C` make angle at most `ε`;
* `sq_norm_le_sub_add_sub`: the two-subspace estimate behind EJZ Lemma 3.1,
  `(1 - ε) ‖w‖² ≤ ‖w - a‖² + ‖w - b‖²` for `a`, `b` the projections of `w` on `ε`-orthogonal
  subspaces.
-/

namespace GroupApproximation

universe v

namespace ThreeVertexClosure

open HilbertEpsilonOrthogonality

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `ε`-orthogonality passes to the topological closures of both subspaces. -/
theorem epsilonOrthogonal_topologicalClosure {X Y : Submodule ℝ E} {epsilon : ℝ}
    (h : EpsilonOrthogonal X Y epsilon) :
    EpsilonOrthogonal X.topologicalClosure Y.topologicalClosure epsilon := by
  have hleft : ∀ w ∈ Y, ∀ u ∈ X.topologicalClosure,
      |inner ℝ u w| ≤ epsilon * ‖u‖ * ‖w‖ := by
    intro w hw u hu
    have hcont : Continuous fun u : E ↦ epsilon * ‖u‖ * ‖w‖ - |inner ℝ u w| :=
      ((continuous_const.mul continuous_norm).mul continuous_const).sub
        (continuous_id.inner continuous_const).abs
    have hsub : (X : Set E) ⊆ {u : E | 0 ≤ epsilon * ‖u‖ * ‖w‖ - |inner ℝ u w|} := by
      intro u' hu'
      exact sub_nonneg.mpr (h u' hu' w hw)
    have hucl : u ∈ closure (X : Set E) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hu
    have hmem : 0 ≤ epsilon * ‖u‖ * ‖w‖ - |inner ℝ u w| :=
      closure_minimal hsub (isClosed_le continuous_const hcont) hucl
    exact sub_nonneg.mp hmem
  intro u hu w hw
  have hcont : Continuous fun w : E ↦ epsilon * ‖u‖ * ‖w‖ - |inner ℝ u w| :=
    (continuous_const.mul continuous_norm).sub (continuous_const.inner continuous_id).abs
  have hsub : (Y : Set E) ⊆ {w : E | 0 ≤ epsilon * ‖u‖ * ‖w‖ - |inner ℝ u w|} := by
    intro w' hw'
    exact sub_nonneg.mpr (hleft w' hw' u hu)
  have hwcl : w ∈ closure (Y : Set E) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hw
  have hmem : 0 ≤ epsilon * ‖u‖ * ‖w‖ - |inner ℝ u w| :=
    closure_minimal hsub (isClosed_le continuous_const hcont) hwcl
  exact sub_nonneg.mp hmem

/-- Inside a closed subspace `V₀` containing `A`, a vector of `V₀` orthogonal to every vector of
`V₀ ⊓ Aᗮ` lies in the closure of `A`. -/
theorem mem_topologicalClosure_of_orthogonal_inf [CompleteSpace E] {V₀ A : Submodule ℝ E}
    (hV₀ : IsClosed (V₀ : Set E)) (hA : A ≤ V₀) {w : E} (hw : w ∈ V₀)
    (horth : ∀ r ∈ V₀ ⊓ Aᗮ, inner ℝ r w = 0) : w ∈ A.topologicalClosure := by
  let C : Submodule ℝ E := A.topologicalClosure
  haveI : CompleteSpace C := (Submodule.isClosed_topologicalClosure A).completeSpace_coe
  have hCV : C ≤ V₀ := Submodule.topologicalClosure_minimal A hA hV₀
  have hpC : C.starProjection w ∈ C := C.starProjection_apply_mem w
  have hrC : w - C.starProjection w ∈ Cᗮ := C.sub_starProjection_mem_orthogonal w
  have hrV : w - C.starProjection w ∈ V₀ := V₀.sub_mem hw (hCV hpC)
  have hrA : w - C.starProjection w ∈ Aᗮ :=
    Submodule.orthogonal_le (Submodule.le_topologicalClosure A) hrC
  have hrw : inner ℝ (w - C.starProjection w) w = 0 := horth _ ⟨hrV, hrA⟩
  have hrp : inner ℝ (w - C.starProjection w) (C.starProjection w) = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hpC hrC
  have hrr : inner ℝ (w - C.starProjection w) (w - C.starProjection w) = 0 := by
    rw [inner_sub_right, hrw, hrp, sub_zero]
  have hr0 : w - C.starProjection w = 0 := inner_self_eq_zero.mp hrr
  have hweq : w = C.starProjection w := sub_eq_zero.mp hr0
  show w ∈ C
  rw [hweq]
  exact hpC

/-- The image of a closure point under a continuous linear map is a closure point of the image
submodule. -/
theorem map_mem_topologicalClosure_map (Q : E →L[ℝ] E) {S : Submodule ℝ E} {t : E}
    (ht : t ∈ S.topologicalClosure) :
    Q t ∈ (S.map (Q : E →ₗ[ℝ] E)).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at ht ⊢
  exact map_mem_closure Q.continuous ht fun x hx ↦ Submodule.mem_map_of_mem hx

/-- An `ε`-orthogonal pair with `ε < 1` has closures meeting only in zero. -/
theorem eq_zero_of_mem_topologicalClosure {X Y : Submodule ℝ E} {epsilon : ℝ}
    (heps1 : epsilon < 1) (h : EpsilonOrthogonal X Y epsilon) {w : E}
    (hX : w ∈ X.topologicalClosure) (hY : w ∈ Y.topologicalClosure) : w = 0 := by
  have hc := epsilonOrthogonal_topologicalClosure h w hX w hY
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖w‖)] at hc
  have hsq : ‖w‖ ^ 2 = 0 := by
    have hnn : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr heps1.le) hnn]
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)

/-- **EJZ (3.3).**  Suppose the projections to `Cᗮ` of `A` and of `B` are `ε`-orthogonal, with
`0 ≤ ε < 1`.  Let `s ⟂ A`, `s ⟂ C`, `t ⟂ B`, `t ⟂ C`, and let `t` lie in the closure of
`A + B + C`.  Then `|⟪s, t⟫| ≤ ε ‖s‖ ‖t‖`.

This is `ThreeVertexDuality.abs_inner_le_of_mem_closure_sup` for the pair `Q(A)`, `Q(B)`,
`Q = P_{Cᗮ}`: `s ⟂ Q(A)` because `Q` is self-adjoint and fixes `s`, and `t = Q t` lies in the
closure of `Q(A + B + C) ⊆ Q(A) + Q(B)`. -/
theorem abs_inner_le_of_projected_angle (A B C : Submodule ℝ E) [C.HasOrthogonalProjection]
    {epsilon : ℝ} (heps0 : 0 ≤ epsilon) (heps1 : epsilon < 1)
    (hang : ∀ a ∈ A, ∀ b ∈ B,
      |inner ℝ (Cᗮ.starProjection a) (Cᗮ.starProjection b)| ≤
        epsilon * ‖Cᗮ.starProjection a‖ * ‖Cᗮ.starProjection b‖)
    {s t : E} (hsA : s ∈ Aᗮ) (hsC : s ∈ Cᗮ) (htB : t ∈ Bᗮ) (htC : t ∈ Cᗮ)
    (ht : t ∈ (A ⊔ B ⊔ C).topologicalClosure) :
    |inner ℝ s t| ≤ epsilon * ‖s‖ * ‖t‖ := by
  let X : Submodule ℝ E := A.map (Cᗮ.starProjection : E →ₗ[ℝ] E)
  let Y : Submodule ℝ E := B.map (Cᗮ.starProjection : E →ₗ[ℝ] E)
  have hXY : EpsilonOrthogonal X Y epsilon := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    exact hang a ha b hb
  have hQs : Cᗮ.starProjection s = s := Submodule.starProjection_eq_self_iff.mpr hsC
  have hQt : Cᗮ.starProjection t = t := Submodule.starProjection_eq_self_iff.mpr htC
  have hsX : s ∈ Xᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    change inner ℝ (Cᗮ.starProjection a) s = 0
    rw [Submodule.inner_starProjection_left_eq_right, hQs]
    exact Submodule.inner_right_of_mem_orthogonal ha hsA
  have htY : t ∈ Yᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    change inner ℝ (Cᗮ.starProjection b) t = 0
    rw [Submodule.inner_starProjection_left_eq_right, hQt]
    exact Submodule.inner_right_of_mem_orthogonal hb htB
  have htcl : t ∈ (X ⊔ Y).topologicalClosure := by
    have h1 := map_mem_topologicalClosure_map (Cᗮ.starProjection) ht
    rw [hQt] at h1
    refine Submodule.topologicalClosure_mono ?_ h1
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
    have hQc : Cᗮ.starProjection c = 0 := Submodule.starProjection_orthogonal_apply_eq_zero hc
    change Cᗮ.starProjection (a + b + c) ∈ X ⊔ Y
    rw [map_add, map_add, hQc, add_zero]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem ha) (Submodule.mem_map_of_mem hb)
  exact ThreeVertexDuality.abs_inner_le_of_mem_closure_sup heps0 heps1 hXY hsX htY htcl

/-- **The two-subspace estimate.**  If `⟪a, w⟫ = ‖a‖²`, `⟪b, w⟫ = ‖b‖²` (as for orthogonal
projections of `w`) and `|⟪a, b⟫| ≤ ε ‖a‖ ‖b‖` with `ε ≥ 0`, then
`(1 - ε) ‖w‖² ≤ ‖w - a‖² + ‖w - b‖²`.

`‖a‖² + ‖b‖² = ⟪a + b, w⟫ ≤ ‖a + b‖ ‖w‖` and `‖a + b‖² ≤ (1 + ε)(‖a‖² + ‖b‖²)`, so
`‖a‖² + ‖b‖² ≤ (1 + ε) ‖w‖²`; and `‖w - a‖² = ‖w‖² - ‖a‖²`. -/
theorem sq_norm_le_sub_add_sub {a b w : E} {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (haw : inner ℝ a w = ‖a‖ ^ 2) (hbw : inner ℝ b w = ‖b‖ ^ 2)
    (hab : |inner ℝ a b| ≤ epsilon * ‖a‖ * ‖b‖) :
    (1 - epsilon) * ‖w‖ ^ 2 ≤ ‖w - a‖ ^ 2 + ‖w - b‖ ^ 2 := by
  have hwa : ‖w - a‖ ^ 2 = ‖w‖ ^ 2 - ‖a‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm a w, haw]
    ring
  have hwb : ‖w - b‖ ^ 2 = ‖w‖ ^ 2 - ‖b‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm b w, hbw]
    ring
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ‖a‖ ^ 2 + ‖b‖ ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]
    positivity
  have hinner : inner ℝ (a + b) w = S := by
    rw [inner_add_left, haw, hbw, hS]
  have hcs : S ≤ ‖a + b‖ * ‖w‖ := by
    rw [← hinner]
    exact real_inner_le_norm (a + b) w
  have hab' : inner ℝ a b ≤ epsilon * ‖a‖ * ‖b‖ := (le_abs_self _).trans hab
  have hnorm : ‖a + b‖ ^ 2 ≤ (1 + epsilon) * S := by
    rw [norm_add_sq_real, hS]
    nlinarith [mul_nonneg heps (sq_nonneg (‖a‖ - ‖b‖))]
  have hsq : S ^ 2 ≤ (1 + epsilon) * S * ‖w‖ ^ 2 := by
    calc
      S ^ 2 ≤ (‖a + b‖ * ‖w‖) ^ 2 := pow_le_pow_left₀ hS0 hcs 2
      _ = ‖a + b‖ ^ 2 * ‖w‖ ^ 2 := by ring
      _ ≤ (1 + epsilon) * S * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hnorm (sq_nonneg _)
  have hmain : S ≤ (1 + epsilon) * ‖w‖ ^ 2 := by
    rcases hS0.eq_or_lt with h0 | hpos
    · rw [← h0]
      exact mul_nonneg (by linarith) (sq_nonneg _)
    · nlinarith
  rw [hwa, hwb]
  nlinarith [hmain, hS]

end ThreeVertexClosure
end GroupApproximation

#audit_axioms GroupApproximation.ThreeVertexClosure.epsilonOrthogonal_topologicalClosure
#audit_axioms GroupApproximation.ThreeVertexClosure.mem_topologicalClosure_of_orthogonal_inf
#audit_axioms GroupApproximation.ThreeVertexClosure.map_mem_topologicalClosure_map
#audit_axioms GroupApproximation.ThreeVertexClosure.eq_zero_of_mem_topologicalClosure
#audit_axioms GroupApproximation.ThreeVertexClosure.abs_inner_le_of_projected_angle
#audit_axioms GroupApproximation.ThreeVertexClosure.sq_norm_le_sub_add_sub
