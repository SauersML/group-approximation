import GroupApproximation.Kazhdan.HilbertEpsilonOrthogonality
import GroupApproximation.Meta.AxiomGuard

/-!
# Duality for epsilon-orthogonal subspaces

Two Hilbert-space lemmas behind the three-subgroup property-(T) criterion of
Ershov--Jaikin-Zapirain (*Property (T) for noncommutative universal lattices*, Invent. Math.
179 (2010), Lemmas 2.4 and 2.5, Proposition 3.2 and Corollary 3.3), which is the criterion
Caprace--Conder--Kaluba--Witzel (arXiv:2011.09276, Theorem 2.6) apply to the Kac--Moody--Steinberg
group `GHB(p)`.

* `abs_inner_le_of_mem_closure_sup` is EJZ Lemma 2.4 in the form that needs only *density* of
  `X + Y`: if `X` and `Y` are `ε`-orthogonal with `ε < 1`, a vector orthogonal to `X` and a vector
  orthogonal to `Y` lying in the closure of `X + Y` make an angle of cosine at most `ε`.  EJZ state
  it for `X + Y` equal to the ambient space; in infinite dimensions the sum need not be closed, and
  the approximating decompositions are kept bounded by `ε < 1`
  (`sq_norm_le_of_epsilonOrthogonal`).
* `epsilonOrthogonal_sup_of_pairwise` is EJZ Lemma 2.5: pairwise angles bound the angle between the
  sum of two subspaces and a third.  The constant is passed as any `ε₀ ≥ 0` with
  `2 max(e₁, e₂)² ≤ ε₀² (1 - e₃)`, which is EJZ's `√2 max{ε₁, ε₂} / √(1 - ε₃)` without a square
  root.
-/

namespace GroupApproximation

universe v

namespace ThreeVertexDuality

open HilbertEpsilonOrthogonality

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An `ε`-orthogonal pair controls each summand by the sum: `(1 - ε²) ‖x‖² ≤ ‖x + y‖²`. -/
theorem sq_norm_le_of_epsilonOrthogonal {X Y : Submodule ℝ E} {epsilon : ℝ}
    (h : EpsilonOrthogonal X Y epsilon) {x y : E} (hx : x ∈ X) (hy : y ∈ Y) :
    (1 - epsilon ^ 2) * ‖x‖ ^ 2 ≤ ‖x + y‖ ^ 2 := by
  have hinner : -(epsilon * ‖x‖ * ‖y‖) ≤ inner ℝ x y := (abs_le.mp (h x hx y hy)).1
  rw [norm_add_sq_real]
  nlinarith [sq_nonneg (‖y‖ - epsilon * ‖x‖)]

/-- The Cauchy--Schwarz step of the duality lemma: if `s ⟂ x`, then
`⟪s, t⟫² ‖x‖² ≤ ‖s‖² (‖t‖² ‖x‖² - ⟪t, x⟫²)`.  It is Cauchy--Schwarz for `s` against
`‖x‖² t - ⟪t, x⟫ x`, whose inner product with `s` is `‖x‖² ⟪s, t⟫`. -/
theorem inner_sq_mul_norm_sq_le {s t x : E} (hsx : inner ℝ s x = 0) :
    inner ℝ s t ^ 2 * ‖x‖ ^ 2 ≤
      ‖s‖ ^ 2 * (‖t‖ ^ 2 * ‖x‖ ^ 2 - inner ℝ t x ^ 2) := by
  by_cases hx : x = 0
  · simp [hx]
  have hxpos : 0 < ‖x‖ ^ 2 := by
    have := norm_pos_iff.mpr hx
    positivity
  let w : E := (‖x‖ ^ 2) • t - (inner ℝ t x) • x
  have hsw : inner ℝ s w = ‖x‖ ^ 2 * inner ℝ s t := by
    simp only [w, inner_sub_right, real_inner_smul_right, hsx]
    ring
  have hww : ‖w‖ ^ 2 = ‖x‖ ^ 2 * (‖t‖ ^ 2 * ‖x‖ ^ 2 - inner ℝ t x ^ 2) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [w, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq t, real_inner_self_eq_norm_sq x, real_inner_comm x t]
    ring
  have hcs : inner ℝ s w ^ 2 ≤ ‖s‖ ^ 2 * ‖w‖ ^ 2 := by
    have hle := abs_real_inner_le_norm s w
    calc
      inner ℝ s w ^ 2 = |inner ℝ s w| ^ 2 := (sq_abs _).symm
      _ ≤ (‖s‖ * ‖w‖) ^ 2 := by gcongr
      _ = ‖s‖ ^ 2 * ‖w‖ ^ 2 := by ring
  rw [hsw, hww] at hcs
  have hscaled :
      ‖x‖ ^ 2 * (inner ℝ s t ^ 2 * ‖x‖ ^ 2) ≤
        ‖x‖ ^ 2 * (‖s‖ ^ 2 * (‖t‖ ^ 2 * ‖x‖ ^ 2 - inner ℝ t x ^ 2)) := by
    calc
      ‖x‖ ^ 2 * (inner ℝ s t ^ 2 * ‖x‖ ^ 2) = (‖x‖ ^ 2 * inner ℝ s t) ^ 2 := by ring
      _ ≤ ‖s‖ ^ 2 * (‖x‖ ^ 2 * (‖t‖ ^ 2 * ‖x‖ ^ 2 - inner ℝ t x ^ 2)) := hcs
      _ = ‖x‖ ^ 2 * (‖s‖ ^ 2 * (‖t‖ ^ 2 * ‖x‖ ^ 2 - inner ℝ t x ^ 2)) := by ring
  exact le_of_mul_le_mul_left hscaled hxpos

/-- **EJZ Lemma 2.4, density form.**  Let `X` and `Y` be `ε`-orthogonal with `0 ≤ ε < 1`.  If
`s ⟂ X`, `t ⟂ Y` and `t` lies in the closure of `X + Y`, then `|⟪s, t⟫| ≤ ε ‖s‖ ‖t‖`.

For `z = x + y` with `x ∈ X`, `y ∈ Y`: `⟪t, z⟫ = ⟪t, x⟫`, Cauchy--Schwarz against `s ⟂ x` gives
`‖s‖² ⟪t, x⟫² ≤ ‖x‖² (‖s‖² ‖t‖² - ⟪s, t⟫²)`, and `(1 - ε²) ‖x‖² ≤ ‖z‖²`.  So the continuous function
`z ↦ (1 - ε²) ‖s‖² ⟪t, z⟫² - ‖z‖² (‖s‖² ‖t‖² - ⟪s, t⟫²)` is nonpositive on `X + Y`, hence on its
closure, and evaluating it at `t` is the claim. -/
theorem abs_inner_le_of_mem_closure_sup {X Y : Submodule ℝ E} {epsilon : ℝ}
    (heps0 : 0 ≤ epsilon) (heps1 : epsilon < 1) (hXY : EpsilonOrthogonal X Y epsilon)
    {s t : E} (hs : s ∈ Xᗮ) (ht : t ∈ Yᗮ) (htmem : t ∈ (X ⊔ Y).topologicalClosure) :
    |inner ℝ s t| ≤ epsilon * ‖s‖ * ‖t‖ := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ‖s‖ ^ 2 * ‖t‖ ^ 2 - inner ℝ s t ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    have hcs := real_inner_mul_inner_self_le s t
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
    rw [ha]
    nlinarith [hcs]
  have h1e : 0 ≤ 1 - epsilon ^ 2 := by nlinarith
  let f : E → ℝ := fun z ↦ (1 - epsilon ^ 2) * ‖s‖ ^ 2 * inner ℝ t z ^ 2 - ‖z‖ ^ 2 * a
  have hf : Continuous f :=
    (continuous_const.mul ((continuous_const.inner continuous_id).pow 2)).sub
      ((continuous_norm.pow 2).mul continuous_const)
  have hsub : ((X ⊔ Y : Submodule ℝ E) : Set E) ⊆ {z : E | f z ≤ 0} := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    have hsx : inner ℝ s x = 0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal X s).mp hs x hx
    have hty : inner ℝ t y = 0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal Y t).mp ht y hy
    have htz : inner ℝ t (x + y) = inner ℝ t x := by
      rw [inner_add_right, hty, add_zero]
    have hI := inner_sq_mul_norm_sq_le (t := t) hsx
    have hII : ‖s‖ ^ 2 * inner ℝ t x ^ 2 ≤ ‖x‖ ^ 2 * a := by
      rw [ha]
      nlinarith [hI]
    have hnorm := sq_norm_le_of_epsilonOrthogonal hXY hx hy
    have h3 : (1 - epsilon ^ 2) * (‖s‖ ^ 2 * inner ℝ t x ^ 2) ≤
        (1 - epsilon ^ 2) * (‖x‖ ^ 2 * a) :=
      mul_le_mul_of_nonneg_left hII h1e
    have h4 : (1 - epsilon ^ 2) * ‖x‖ ^ 2 * a ≤ ‖x + y‖ ^ 2 * a :=
      mul_le_mul_of_nonneg_right hnorm ha0
    show (1 - epsilon ^ 2) * ‖s‖ ^ 2 * inner ℝ t (x + y) ^ 2 - ‖x + y‖ ^ 2 * a ≤ 0
    rw [htz]
    nlinarith [h3, h4]
  have hclosed : IsClosed {z : E | f z ≤ 0} := isClosed_le hf continuous_const
  have hcl : t ∈ closure ((X ⊔ Y : Submodule ℝ E) : Set E) := by
    rw [← Submodule.topologicalClosure_coe]
    exact htmem
  have htf : (1 - epsilon ^ 2) * ‖s‖ ^ 2 * inner ℝ t t ^ 2 - ‖t‖ ^ 2 * a ≤ 0 :=
    closure_minimal hsub hclosed hcl
  rw [real_inner_self_eq_norm_sq] at htf
  by_cases ht0 : t = 0
  · simp [ht0]
  have htpos : 0 < ‖t‖ ^ 2 := by
    have := norm_pos_iff.mpr ht0
    positivity
  have hmain : (1 - epsilon ^ 2) * ‖s‖ ^ 2 * ‖t‖ ^ 2 ≤ a := by
    have hscaled : ‖t‖ ^ 2 * ((1 - epsilon ^ 2) * ‖s‖ ^ 2 * ‖t‖ ^ 2) ≤ ‖t‖ ^ 2 * a := by
      calc
        ‖t‖ ^ 2 * ((1 - epsilon ^ 2) * ‖s‖ ^ 2 * ‖t‖ ^ 2) =
            (1 - epsilon ^ 2) * ‖s‖ ^ 2 * (‖t‖ ^ 2) ^ 2 := by ring
        _ ≤ ‖t‖ ^ 2 * a := by linarith
    exact le_of_mul_le_mul_left hscaled htpos
  have hsq : inner ℝ s t ^ 2 ≤ (epsilon * ‖s‖ * ‖t‖) ^ 2 := by
    rw [ha] at hmain
    have hexp : (epsilon * ‖s‖ * ‖t‖) ^ 2 = epsilon ^ 2 * (‖s‖ ^ 2 * ‖t‖ ^ 2) := by ring
    rw [hexp]
    nlinarith [hmain]
  have hnonneg : 0 ≤ epsilon * ‖s‖ * ‖t‖ := by positivity
  apply (sq_le_sq₀ (abs_nonneg _) hnonneg).mp
  rw [sq_abs]
  exact hsq

/-- **EJZ Lemma 2.5.**  If `T₁ ⊥_{e₃} T₂`, `T₁ ⊥_{e₂} T₃`, `T₂ ⊥_{e₁} T₃` and `0 ≤ e₃ < 1`, then
`T₁ + T₂` and `T₃` are `ε₀`-orthogonal for every `ε₀ ≥ 0` with `2 max(e₁, e₂)² ≤ ε₀² (1 - e₃)`.

`|⟪x + y, z⟫| ≤ max(e₁, e₂) (‖x‖ + ‖y‖) ‖z‖`, `(‖x‖ + ‖y‖)² ≤ 2 (‖x‖² + ‖y‖²)`, and
`(1 - e₃) (‖x‖² + ‖y‖²) ≤ ‖x + y‖²`. -/
theorem epsilonOrthogonal_sup_of_pairwise {T₁ T₂ T₃ : Submodule ℝ E}
    {e₁ e₂ e₃ epsilon₀ : ℝ} (he₁ : 0 ≤ e₁) (he₃ : 0 ≤ e₃) (heps₀ : 0 ≤ epsilon₀)
    (hconst : 2 * max e₁ e₂ ^ 2 ≤ epsilon₀ ^ 2 * (1 - e₃))
    (h₁₂ : EpsilonOrthogonal T₁ T₂ e₃) (h₁₃ : EpsilonOrthogonal T₁ T₃ e₂)
    (h₂₃ : EpsilonOrthogonal T₂ T₃ e₁) :
    EpsilonOrthogonal (T₁ ⊔ T₂) T₃ epsilon₀ := by
  intro w hw z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max e₁ e₂ := ⟨_, rfl⟩
  rw [← hm] at hconst
  have hm1 : e₁ ≤ m := hm ▸ le_max_left _ _
  have hm2 : e₂ ≤ m := hm ▸ le_max_right _ _
  have hm0 : 0 ≤ m := le_trans he₁ hm1
  have hsum : |inner ℝ (x + y) z| ≤ m * (‖x‖ + ‖y‖) * ‖z‖ := by
    rw [inner_add_left]
    calc
      |inner ℝ x z + inner ℝ y z| ≤ |inner ℝ x z| + |inner ℝ y z| := abs_add_le _ _
      _ ≤ e₂ * ‖x‖ * ‖z‖ + e₁ * ‖y‖ * ‖z‖ := add_le_add (h₁₃ x hx z hz) (h₂₃ y hy z hz)
      _ ≤ m * ‖x‖ * ‖z‖ + m * ‖y‖ * ‖z‖ := by gcongr
      _ = m * (‖x‖ + ‖y‖) * ‖z‖ := by ring
  have htrans : (1 - e₃) * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ ‖x + y‖ ^ 2 := by
    have hinner : -(e₃ * ‖x‖ * ‖y‖) ≤ inner ℝ x y := (abs_le.mp (h₁₂ x hx y hy)).1
    rw [norm_add_sq_real]
    nlinarith [mul_nonneg he₃ (sq_nonneg (‖x‖ - ‖y‖))]
  have hbound : m * (‖x‖ + ‖y‖) ≤ epsilon₀ * ‖x + y‖ := by
    have hl : 0 ≤ m * (‖x‖ + ‖y‖) := by positivity
    have hr : 0 ≤ epsilon₀ * ‖x + y‖ := by positivity
    apply (sq_le_sq₀ hl hr).mp
    have h2 : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    have hS : 0 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by positivity
    calc
      (m * (‖x‖ + ‖y‖)) ^ 2 = m ^ 2 * (‖x‖ + ‖y‖) ^ 2 := by ring
      _ ≤ m ^ 2 * (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg m)
      _ = (2 * m ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by ring
      _ ≤ (epsilon₀ ^ 2 * (1 - e₃)) * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hconst hS
      _ = epsilon₀ ^ 2 * ((1 - e₃) * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by ring
      _ ≤ epsilon₀ ^ 2 * ‖x + y‖ ^ 2 :=
        mul_le_mul_of_nonneg_left htrans (sq_nonneg epsilon₀)
      _ = (epsilon₀ * ‖x + y‖) ^ 2 := by ring
  calc
    |inner ℝ (x + y) z| ≤ m * (‖x‖ + ‖y‖) * ‖z‖ := hsum
    _ ≤ epsilon₀ * ‖x + y‖ * ‖z‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg z)

end ThreeVertexDuality
end GroupApproximation

#audit_axioms GroupApproximation.ThreeVertexDuality.sq_norm_le_of_epsilonOrthogonal
#audit_axioms GroupApproximation.ThreeVertexDuality.inner_sq_mul_norm_sq_le
#audit_axioms GroupApproximation.ThreeVertexDuality.abs_inner_le_of_mem_closure_sup
#audit_axioms GroupApproximation.ThreeVertexDuality.epsilonOrthogonal_sup_of_pairwise
