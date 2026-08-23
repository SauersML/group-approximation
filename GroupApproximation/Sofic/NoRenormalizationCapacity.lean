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

open Matrix KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

/-! ## The packet collision estimate -/

/-- **Collision kills the phase.**  If `A` and `Bv` are unitary, the local
packet is approximately `A * Bv = Z * Bv * A`, the cross packet approximately
commutes `A` with `Bw`, and `Bv` and `Bw` collide, then `Z` is close to the
identity. -/
theorem collision_kills_phase {Y : Type*} [Fintype Y] [DecidableEq Y]
    [Nonempty Y]
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
    {Y V C : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
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

/-! ## Spectral recurrence versus a uniformly authenticated power return -/

/-- Every finite-dimensional unitary has a positive power arbitrarily close
to the identity in operator norm.  Compactness of the bounded power orbit is
enough here; the sharper explicit bound `m ≤ Q ^ d` used in the paper route is
not needed by the Power-Return contradiction. -/
theorem exists_positive_power_opNorm_sub_one_lt
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {W : Matrix Y Y ℂ} (hW : W ∈ Matrix.unitaryGroup Y ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ‖W ^ m - 1‖ < ε := by
  have hpow_unitary : ∀ n : ℕ, W ^ n ∈ Matrix.unitaryGroup Y ℂ :=
    fun n ↦ (Matrix.unitaryGroup Y ℂ).pow_mem hW n
  have hpow_mem : ∀ n : ℕ, W ^ n ∈ Metric.closedBall (0 : Matrix Y Y ℂ) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right,
      CStarRing.norm_of_mem_unitary (hpow_unitary n)]
  obtain ⟨limit, _hlimit, φ, hφ, htend⟩ :=
    (isCompact_closedBall (0 : Matrix Y Y ℂ) 1).tendsto_subseq hpow_mem
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htend (ε / 2) (by positivity)
  let i := φ N
  let j := φ (N + 1)
  have hij : i < j := hφ (Nat.lt_succ_self N)
  have hi : dist (W ^ i) limit < ε / 2 := hN N le_rfl
  have hj : dist (W ^ j) limit < ε / 2 := hN (N + 1) (Nat.le_succ N)
  have hd : dist (W ^ j) (W ^ i) < ε := by
    calc
      dist (W ^ j) (W ^ i) ≤ dist (W ^ j) limit + dist limit (W ^ i) :=
        dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hj (by simpa [dist_comm] using hi)
      _ = ε := by ring
  let m := j - i
  have hm : 0 < m := Nat.sub_pos_of_lt hij
  have hij_add : i + m = j := Nat.add_sub_of_le hij.le
  have hfactor : W ^ j - W ^ i = W ^ i * (W ^ m - 1) := by
    rw [← hij_add, pow_add]
    noncomm_ring
  refine ⟨m, hm, ?_⟩
  calc
    ‖W ^ m - 1‖ = ‖W ^ i * (W ^ m - 1)‖ :=
      (CStarRing.norm_mem_unitary_mul _ (hpow_unitary i)).symm
    _ = ‖W ^ j - W ^ i‖ := by rw [hfactor]
    _ = dist (W ^ j) (W ^ i) := by rw [dist_eq_norm]
    _ < ε := hd

/-- A recurrent power cannot be close to a unitary conjugate of a cursor that
stays separated from the identity.  This is the quantitative core of the
Power-Return criterion: conjugation preserves the cursor's operator-norm
distance from `1`, while the selected power has returned close to `1`.

The theorem deliberately assumes the recurrent exponent as input.  Producing
such an exponent for every finite-dimensional unitary is the separate
finite-spectrum recurrence lemma; compiling all corresponding word checks
with one error budget is the open UPR interface. -/
theorem recurrent_power_far_from_unitary_conjugate
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {A W : Matrix Y Y ℂ} {m : ℕ} {β : ℝ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hsep : β ≤ ‖W - 1‖)
    (hreturn : ‖W ^ m - 1‖ ≤ β / 4) :
    3 * β / 4 ≤ ‖A * W * Aᴴ - W ^ m‖ := by
  have hconj_matrix : A * W * Aᴴ - 1 = A * (W - 1) * Aᴴ := by
    have hAA : A * Aᴴ = 1 := Unitary.mul_star_self_of_mem hA
    calc
      A * W * Aᴴ - 1 = A * W * Aᴴ - A * Aᴴ := by rw [hAA]
      _ = A * (W - 1) * Aᴴ := by noncomm_ring
  have hconj_norm : ‖A * W * Aᴴ - 1‖ = ‖W - 1‖ := by
    have hAstar : Aᴴ ∈ Matrix.unitaryGroup Y ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      exact Unitary.star_mul_self_of_mem hA
    rw [hconj_matrix, CStarRing.norm_mul_mem_unitary _ hAstar,
      CStarRing.norm_mem_unitary_mul _ hA]
  have htriangle :
      ‖A * W * Aᴴ - 1‖ ≤
        ‖A * W * Aᴴ - W ^ m‖ + ‖W ^ m - 1‖ := by
    calc
      ‖A * W * Aᴴ - 1‖ =
          ‖(A * W * Aᴴ - W ^ m) + (W ^ m - 1)‖ := by
            congr 1
            noncomm_ring
      _ ≤ ‖A * W * Aᴴ - W ^ m‖ + ‖W ^ m - 1‖ := norm_add_le _ _
  rw [hconj_norm] at htriangle
  linarith

/-- **Frozen-coordinate Power-Return contradiction.**  If a cursor is
`β`-separated, one of its powers has returned within `β/4`, the authenticated
power-return check costs at most `C * defect`, and that root budget is below
`β/2`, then the finite coordinate cannot exist.

This is the formally checked post-coordinate argument used by the Cairn node
`spectral-recurrence-power-return-non-mf-criterion`.  It has no trace,
property-`(T)`, projection, central-sign, or literature hypothesis. -/
theorem no_model_of_recurrent_uniform_power_return
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {A W : Matrix Y Y ℂ} {m : ℕ} {β C defect : ℝ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hβ : 0 < β)
    (hsep : β ≤ ‖W - 1‖)
    (hreturn : ‖W ^ m - 1‖ ≤ β / 4)
    (hauth : ‖A * W * Aᴴ - W ^ m‖ ≤ C * defect)
    (hbudget : C * defect < β / 2) : False := by
  have hlower : 3 * β / 4 ≤ ‖A * W * Aᴴ - W ^ m‖ :=
    recurrent_power_far_from_unitary_conjugate hA hsep hreturn
  linarith

/-- **Spectral-recurrence Power-Return criterion at one coordinate.**  A
finite-dimensional unitary cursor cannot stay `β`-separated while every
positive conjugacy-to-power challenge is authenticated by the same root
budget.  The recurrent exponent is selected by the proof after this finite
coordinate is fixed; neither the challenge family nor a program has to read
the dimension. -/
theorem no_model_of_uniform_power_return
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {W : Matrix Y Y ℂ} (hW : W ∈ Matrix.unitaryGroup Y ℂ)
    (A : ℕ → Matrix Y Y ℂ)
    (hA : ∀ m, A m ∈ Matrix.unitaryGroup Y ℂ)
    {β C defect : ℝ} (hβ : 0 < β)
    (hsep : β ≤ ‖W - 1‖)
    (hauth : ∀ m, 0 < m → ‖A m * W * (A m)ᴴ - W ^ m‖ ≤ C * defect)
    (hbudget : C * defect < β / 2) : False := by
  obtain ⟨m, hm, hreturn⟩ :=
    exists_positive_power_opNorm_sub_one_lt hW (show 0 < β / 4 by positivity)
  exact no_model_of_recurrent_uniform_power_return (hA m) hβ hsep hreturn.le
    (hauth m hm) hbudget

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
  exact hab (Nat.pow_left_injective (Nat.ne_of_gt hk) hpowers)

end NoRenormalizationCapacity
end GroupApproximation
