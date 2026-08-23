import GroupApproximation.Sofic.InvolutionRankMass

/-!
# Operator-norm collision and finite-capacity detectors

This file formalizes the unconditional analytic and combinatorial core of the
no-renormalization MF programme.

The results here do **not** assert that a finite presentation implementing the
required depth-uniform self-hash has already been constructed.  They isolate
what such a compiler may use once its word-level authentication theorem is
available:

* two nearby packet states, one twisted local check, and one cross check force
  the marked phase close to `1` in operator norm;
* a finite coloring/cover of the unitary group therefore bounds every
  authenticated challenge graph;
* a uniformly authenticated unbounded challenge family defeats each fixed
  finite-dimensional model after its dimension is known;
* projection distance `< 1` converts approximate transport into exact rank,
  and a nontrivial multiplicative rank monodromy forces rank zero.

There is no normalized trace and no Hilbert--Schmidt renormalization in these
statements.
-/

namespace GroupApproximation
namespace NoRenormalizationCapacity

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## The packet collision estimate -/

/-- **Collision kills the phase.**  If `A` and `Bv` are unitary, the local
packet is approximately `A * Bv = Z * Bv * A`, the cross packet approximately
commutes `A` with `Bw`, and `Bv` and `Bw` collide, then `Z` is close to the
identity. -/
theorem collision_kills_phase {Y : Type*} [Fintype Y] [DecidableEq Y]
    {A Bv Bw Z : Matrix Y Y ℂ} {ε δ : ℝ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hBv : Bv ∈ Matrix.unitaryGroup Y ℂ)
    (hlocal : ‖A * Bv - Z * Bv * A‖ ≤ ε)
    (hcross : ‖A * Bw - Bw * A‖ ≤ ε)
    (hclose : ‖Bv - Bw‖ ≤ δ) :
    ‖Z - 1‖ ≤ 2 * δ + 2 * ε := by
  have hAone : ‖A‖ = 1 := CStarRing.norm_of_mem_unitary hA
  have hclose' : ‖Bw - Bv‖ ≤ δ := by
    rwa [norm_sub_rev]
  have hleft : ‖A * (Bv - Bw)‖ ≤ δ := by
    calc
      ‖A * (Bv - Bw)‖ ≤ ‖A‖ * ‖Bv - Bw‖ := norm_mul_le _ _
      _ = ‖Bv - Bw‖ := by rw [hAone, one_mul]
      _ ≤ δ := hclose
  have hright : ‖(Bw - Bv) * A‖ ≤ δ := by
    calc
      ‖(Bw - Bv) * A‖ ≤ ‖Bw - Bv‖ * ‖A‖ := norm_mul_le _ _
      _ = ‖Bw - Bv‖ := by rw [hAone, mul_one]
      _ ≤ δ := hclose'
  have hcomm : ‖A * Bv - Bv * A‖ ≤ 2 * δ + ε := by
    have hsplit :
        A * Bv - Bv * A =
          A * (Bv - Bw) + (A * Bw - Bw * A) + (Bw - Bv) * A := by
      noncomm_ring
    rw [hsplit]
    calc
      ‖A * (Bv - Bw) + (A * Bw - Bw * A) + (Bw - Bv) * A‖
          ≤ ‖A * (Bv - Bw)‖ + ‖A * Bw - Bw * A‖ +
              ‖(Bw - Bv) * A‖ := by
            exact (norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ δ + ε + δ := add_le_add (add_le_add hleft hcross) hright
      _ = 2 * δ + ε := by ring
  have hphase : ‖(Z - 1) * Bv * A‖ ≤ 2 * δ + 2 * ε := by
    have hsplit :
        (Z - 1) * Bv * A =
          -(A * Bv - Z * Bv * A) + (A * Bv - Bv * A) := by
      noncomm_ring
    rw [hsplit]
    calc
      ‖-(A * Bv - Z * Bv * A) + (A * Bv - Bv * A)‖
          ≤ ‖-(A * Bv - Z * Bv * A)‖ + ‖A * Bv - Bv * A‖ :=
            norm_add_le _ _
      _ = ‖A * Bv - Z * Bv * A‖ + ‖A * Bv - Bv * A‖ := by
            rw [norm_neg]
      _ ≤ ε + (2 * δ + ε) := add_le_add hlocal hcomm
      _ = 2 * δ + 2 * ε := by ring
  calc
    ‖Z - 1‖ = ‖(Z - 1) * Bv * A‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ hA,
        CStarRing.norm_mul_mem_unitary _ hBv]
    _ ≤ 2 * δ + 2 * ε := hphase

/-! ## Finite-color collision -/

/-- An abstract high-chromatic challenge: every coloring by the finite palette
`C` gives one adjacent monochromatic pair.  This formulation avoids committing
the collision theorem to a particular graph library. -/
def DefeatsPalette {V C : Type*} (Adjacent : V → V → Prop) : Prop :=
  ∀ color : V → C, ∃ v w, Adjacent v w ∧ color v = color w

/-- A finite cover converts a palette-defeating challenge into a state
collision. -/
theorem exists_adjacent_close_of_defeatsPalette
    {V C State : Type*} {Adjacent : V → V → Prop}
    (hchallenge : DefeatsPalette (C := C) Adjacent)
    (state : V → State) (color : State → C)
    (dist : State → State → ℝ) {δ : ℝ}
    (hsame : ∀ X Y, color X = color Y → dist X Y ≤ δ) :
    ∃ v w, Adjacent v w ∧ dist (state v) (state w) ≤ δ := by
  obtain ⟨v, w, hadj, hcolor⟩ := hchallenge (fun x ↦ color (state x))
  exact ⟨v, w, hadj, hsame _ _ hcolor⟩

/-- **Chromatic packet collapse.**  Once a finite operator-norm cover assigns
colors with same-color diameter at most `δ`, a challenge defeating that
palette supplies an adjacent collision and the packet estimate forces the
phase close to `1`. -/
theorem phase_close_of_palette_overflow
    {Y V C : Type*} [Fintype Y] [DecidableEq Y]
    {Adjacent : V → V → Prop}
    (hchallenge : DefeatsPalette (C := C) Adjacent)
    (A B : V → Matrix Y Y ℂ) (Z : Matrix Y Y ℂ)
    (color : Matrix Y Y ℂ → C) {ε δ : ℝ}
    (hA : ∀ v, A v ∈ Matrix.unitaryGroup Y ℂ)
    (hB : ∀ v, B v ∈ Matrix.unitaryGroup Y ℂ)
    (hlocal : ∀ v, ‖A v * B v - Z * B v * A v‖ ≤ ε)
    (hcross : ∀ v w, Adjacent v w →
      ‖A v * B w - B w * A v‖ ≤ ε)
    (hsame : ∀ X Y, color X = color Y → ‖X - Y‖ ≤ δ) :
    ‖Z - 1‖ ≤ 2 * δ + 2 * ε := by
  obtain ⟨v, w, hadj, hclose⟩ :=
    exists_adjacent_close_of_defeatsPalette hchallenge B color
      (fun X Y ↦ ‖X - Y‖) hsame
  exact collision_kills_phase (hA v) (hB v)
    (hlocal v) (hcross v w hadj) hclose

/-! ## The post-coordinate capacity diagonal -/

/-- A fixed finite model cannot satisfy a uniformly authenticated unbounded
family of finite-capacity challenges.  The challenge index is chosen by the
proof after the model and its dimension are fixed. -/
theorem no_model_of_uniform_unbounded_capacity
    {Model : Type*} (dimension : Model → ℕ) (capacity : ℕ → ℕ)
    (valid : ℕ → Model → Prop)
    (hunbounded : ∀ d, ∃ n, d < capacity n)
    (U : Model) (hall : ∀ n, valid n U)
    (hsound : ∀ n, valid n U → capacity n ≤ dimension U) : False := by
  obtain ⟨n, hn⟩ := hunbounded (dimension U)
  exact (not_lt_of_ge (hsound n (hall n))) hn

/-! ## Rank monodromy -/

/-- The analytic edge of rank monodromy is already the rank-rigidity theorem:
orthogonal projections at operator distance `< 1` have exactly equal rank. -/
theorem projection_rank_rigid {Y : Type*} [Fintype Y] [DecidableEq Y]
    {p q : Matrix Y Y ℂ}
    (hp : IsOrthogonalProjectionMatrix p)
    (hq : IsOrthogonalProjectionMatrix q) (hlt : ‖p - q‖ < 1) :
    p.rank = q.rank :=
  InvolutionRankMass.rank_eq_of_projections_close hp hq hlt

/-- The integer endpoint of a closed rank cycle.  If traversing a nonempty
cycle multiplies a finite rank by `a^k` on one decoding and by `b^k` on the
other, with `a ≠ b`, the rank is zero. -/
theorem rank_zero_of_power_monodromy {a b k r : ℕ}
    (hk : 0 < k) (hab : a ≠ b) (hcycle : a ^ k * r = b ^ k * r) :
    r = 0 := by
  by_contra hr
  have hpowers : a ^ k = b ^ k := mul_right_cancel₀ hr hcycle
  exact hab (Nat.pow_left_injective hk hpowers)

end NoRenormalizationCapacity
end GroupApproximation
