import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.Stab
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Matrix units and the vector state of `𝒦 = Stab ℂ`

Preparation for the rank of projections in the compact operators `𝒦 = Stab ℂ` (Blackadar,
*K-Theory for Operator Algebras*, 4.2 and 5.1). With `e = π(1)` the unit of `ℂ` in the faithful
representation and `E i j = e_{ij} ⊗ e`:

* `E i j * E k l = δ_{jk} E i l` and `star (E i j) = E j i`;
* every finite matrix lies in the span `C N` of the `E i j` with `i, j < N`;
* **compression**: `E 0 0 * x * E 0 0 = ω x • E 0 0` for `x ∈ Stab ℂ`, where `ω` is the vector
  state of a unit vector `ξ` in the range of `E 0 0`;
* **columns** (`y ∈ Stab ℂ` with `y * E 0 0 = y`) satisfy `star y * z = ⟪y ξ, z ξ⟫ • E 0 0` and
  `E i j * y = ω (E 0 j * y) • E i 0`;
* an operator killing every `E i 0` kills `Stab ℂ`.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-C1, work order WO-TWWKK-C1).
-/

namespace GroupApproximation.Full.TWWKK

noncomputable section

namespace StabRankAux

open Stab

/-! ## Matrix units of `𝒦` -/

/-- The unit of `ℂ` in the faithful representation. -/
def e : RepSpace ℂ →L[ℂ] RepSpace ℂ :=
  rep ℂ 1

theorem e_mul_self : e * e = e := by
  show rep ℂ 1 * rep ℂ 1 = rep ℂ 1
  rw [← map_mul (rep ℂ) 1 1, mul_one]

theorem star_e : star e = e := by
  show star (rep ℂ 1) = rep ℂ 1
  rw [← map_star (rep ℂ) 1, star_one]

theorem e_ne_zero : e ≠ 0 := by
  intro h
  have h1 : rep ℂ (1 : ℂ) = rep ℂ 0 := by
    rw [map_zero]
    exact h
  exact one_ne_zero (rep_injective ℂ h1)

theorem rep_eq_smul (z : ℂ) : rep ℂ z = z • e := by
  show rep ℂ z = z • rep ℂ 1
  rw [show z • rep ℂ 1 = rep ℂ (z • 1) from (map_smul (rep ℂ) z 1).symm, smul_eq_mul, mul_one]

/-- The matrix unit `e_{ij}` of `𝒦`. -/
def E (i j : ℕ) : Ambient ℂ :=
  matUnit ℂ i j e

theorem E_mul (i j k l : ℕ) : E i j * E k l = if j = k then E i l else 0 := by
  show matUnit ℂ i j e * matUnit ℂ k l e = if j = k then matUnit ℂ i l e else 0
  rw [matUnit_mul_matUnit, e_mul_self]

theorem E_mul_self (i j l : ℕ) : E i j * E j l = E i l := by
  rw [E_mul, if_pos rfl]

theorem E_mul_of_ne {j k : ℕ} (h : j ≠ k) (i l : ℕ) : E i j * E k l = 0 := by
  rw [E_mul, if_neg h]

theorem star_E (i j : ℕ) : star (E i j) = E j i := by
  show star (matUnit ℂ i j e) = matUnit ℂ j i e
  rw [star_matUnit, star_e]

theorem E_mem_finiteMatrices (i j : ℕ) : E i j ∈ finiteMatrices ℂ :=
  matUnit_rep_mem_finiteMatrices i j 1

theorem E_mem (i j : ℕ) : E i j ∈ closedSubalgebra ℂ :=
  matUnit_rep_mem i j 1

theorem matUnit_rep (i j : ℕ) (b : ℂ) : matUnit ℂ i j (rep ℂ b) = b • E i j := by
  show matUnit ℂ i j (rep ℂ b) = b • matUnit ℂ i j e
  rw [rep_eq_smul, matUnit_smul]

/-! ## Finite matrices -/

/-- The matrix units `E i j` with `i, j < N`. -/
def corners (N : ℕ) : Set (Ambient ℂ) :=
  {x | ∃ i j, i < N ∧ j < N ∧ x = E i j}

/-- The `N × N` matrices of `𝒦`. -/
def C (N : ℕ) : Submodule ℂ (Ambient ℂ) :=
  Submodule.span ℂ (corners N)

theorem E_mem_C {N i j : ℕ} (hi : i < N) (hj : j < N) : E i j ∈ C N :=
  Submodule.subset_span ⟨i, j, hi, hj, rfl⟩

theorem C_mono {N M : ℕ} (h : N ≤ M) : C N ≤ C M := by
  refine Submodule.span_mono ?_
  intro x hx
  obtain ⟨i, j, hi, hj, rfl⟩ := hx
  exact ⟨i, j, lt_of_lt_of_le hi h, lt_of_lt_of_le hj h, rfl⟩

theorem C_mul_mem {N : ℕ} {a b : Ambient ℂ} (ha : a ∈ C N) (hb : b ∈ C N) : a * b ∈ C N := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, j, hi, _, rfl⟩ := hx
      obtain ⟨k, l, _, hl, rfl⟩ := hy
      rw [E_mul]
      split_ifs
      · exact E_mem_C hi hl
      · exact zero_mem _
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem star_mem_C {N : ℕ} {a : Ambient ℂ} (ha : a ∈ C N) : star a ∈ C N := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, j, hi, hj, rfl⟩ := hx
    rw [star_E]
    exact E_mem_C hj hi
  | zero => rw [star_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
  | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ (star c) hx

/-- Every finite matrix of `𝒦` is an `N × N` matrix for some `N`. -/
theorem exists_C {x : Ambient ℂ} (hx : x ∈ finiteMatrices ℂ) : ∃ N, x ∈ C N := by
  change x ∈ NonUnitalStarAlgebra.adjoin ℂ (generators ℂ) at hx
  induction hx using NonUnitalStarAlgebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, j, b, rfl⟩ : ∃ (i j : ℕ) (b : ℂ), x = matUnit ℂ i j (rep ℂ b) := hx
    refine ⟨max i j + 1, ?_⟩
    rw [matUnit_rep]
    exact Submodule.smul_mem _ b
      (E_mem_C (Nat.lt_succ_of_le (le_max_left i j)) (Nat.lt_succ_of_le (le_max_right i j)))
  | add x y _ _ hx hy =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hy
    exact ⟨max N M, add_mem (C_mono (le_max_left N M) hN) (C_mono (le_max_right N M) hM)⟩
  | zero => exact ⟨0, zero_mem _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hy
    exact ⟨max N M, C_mul_mem (C_mono (le_max_left N M) hN) (C_mono (le_max_right N M) hM)⟩
  | smul c x _ hx =>
    obtain ⟨N, hN⟩ := hx
    exact ⟨N, Submodule.smul_mem _ c hN⟩
  | star x _ hx =>
    obtain ⟨N, hN⟩ := hx
    exact ⟨N, star_mem_C hN⟩

/-! ## Compression to the corner -/

theorem compress_C {N : ℕ} {y : Ambient ℂ} (hy : y ∈ C N) : E 0 0 * y * E 0 0 ∈ ℂ ∙ E 0 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, j, _, _, rfl⟩ := hx
    by_cases hi : 0 = i
    · by_cases hj : j = 0
      · rw [E_mul 0 0 i j, if_pos hi, E_mul 0 j 0 0, if_pos hj]
        exact Submodule.mem_span_singleton_self _
      · rw [E_mul 0 0 i j, if_pos hi, E_mul 0 j 0 0, if_neg hj]
        exact zero_mem _
    · rw [E_mul 0 0 i j, if_neg hi, zero_mul]
      exact zero_mem _
  | zero => rw [mul_zero, zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [mul_add, add_mul]; exact add_mem hx hz
  | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem compress_mem {x : Ambient ℂ} (hx : x ∈ closedSubalgebra ℂ) :
    E 0 0 * x * E 0 0 ∈ ℂ ∙ E 0 0 := by
  have hcont : Continuous fun y : Ambient ℂ => E 0 0 * y * E 0 0 :=
    (continuous_const_mul (E 0 0)).mul continuous_const
  have hcl : IsClosed ((fun y : Ambient ℂ => E 0 0 * y * E 0 0) ⁻¹'
      ((ℂ ∙ E 0 0 : Submodule ℂ (Ambient ℂ)) : Set (Ambient ℂ))) :=
    IsClosed.preimage hcont (Submodule.closed_of_finiteDimensional (ℂ ∙ E 0 0))
  have hsub : (finiteMatrices ℂ : Set (Ambient ℂ)) ⊆ (fun y : Ambient ℂ => E 0 0 * y * E 0 0) ⁻¹'
      ((ℂ ∙ E 0 0 : Submodule ℂ (Ambient ℂ)) : Set (Ambient ℂ)) := by
    intro y hy
    obtain ⟨N, hN⟩ := exists_C hy
    exact compress_C hN
  have hx' : x ∈ closure (finiteMatrices ℂ : Set (Ambient ℂ)) := hx
  exact closure_minimal hsub hcl hx'

/-! ## A unit vector in the range of `E 0 0` -/

theorem exists_vec : ∃ v : RepSpace ℂ, e v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact e_ne_zero (ContinuousLinearMap.ext fun v =>
    (hcon v).trans (ContinuousLinearMap.zero_apply v).symm)

/-- A vector not killed by `e`. -/
def v0 : RepSpace ℂ :=
  Classical.choose exists_vec

theorem e_v0 : e v0 ≠ 0 :=
  Classical.choose_spec exists_vec

/-- The vector `δ₀ ⊗ e v₀` of `ℓ²(ℕ, H)`. -/
def eta0 : Space ℂ :=
  lp.single 2 0 (e v0)

theorem eta0_zero : eta0 0 = e v0 :=
  lp.single_apply_self (E := fun _ : ℕ => RepSpace ℂ) 2 0 (e v0)

theorem E00_eta0 : E 0 0 eta0 = eta0 := by
  show (lp.single 2 0 (e (eta0 0)) : Space ℂ) = (lp.single 2 0 (e v0) : Space ℂ)
  have h2 : e (e v0) = e v0 := by
    show (e * e) v0 = e v0
    rw [e_mul_self]
  rw [eta0_zero, h2]

theorem eta0_ne : eta0 ≠ 0 := by
  intro h
  have h3 : eta0 0 = (0 : Space ℂ) 0 := congrArg (fun z : Space ℂ => z 0) h
  rw [lp.coeFn_zero, Pi.zero_apply, eta0_zero] at h3
  exact e_v0 h3

/-- **The unit vector** `ξ = η₀ / ‖η₀‖`, fixed by `E 0 0`. -/
def xi : Space ℂ :=
  (‖eta0‖⁻¹ : ℂ) • eta0

theorem norm_xi : ‖xi‖ = 1 :=
  norm_smul_inv_norm (𝕜 := ℂ) eta0_ne

theorem inner_xi_xi : inner ℂ xi xi = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_xi]
  norm_num

theorem E00_xi : E 0 0 xi = xi := by
  show E 0 0 ((‖eta0‖⁻¹ : ℂ) • eta0) = (‖eta0‖⁻¹ : ℂ) • eta0
  rw [map_smul, E00_eta0]

theorem inner_xi_E00 (w : Space ℂ) : inner ℂ xi (E 0 0 w) = inner ℂ xi w := by
  have h := ContinuousLinearMap.adjoint_inner_right (E 0 0) xi w
  rw [← ContinuousLinearMap.star_eq_adjoint, star_E, E00_xi] at h
  exact h

theorem E00_ne : E 0 0 ≠ 0 := by
  intro h
  have h3 : E 0 0 xi = (0 : Ambient ℂ) xi := congrArg (fun T : Ambient ℂ => T xi) h
  have h1 : xi = 0 := by
    rw [ContinuousLinearMap.zero_apply, E00_xi] at h3
    exact h3
  have h2 := inner_xi_xi
  rw [h1, inner_zero_left] at h2
  exact zero_ne_one h2

/-- **The vector state** `ω x = ⟪ξ, x ξ⟫`. -/
def vst (x : Ambient ℂ) : ℂ :=
  inner ℂ xi (x xi)

/-- **Compression**: `E 0 0 * x * E 0 0 = ω x • E 0 0` on `𝒦`. -/
theorem compress {x : Ambient ℂ} (hx : x ∈ closedSubalgebra ℂ) :
    E 0 0 * x * E 0 0 = vst x • E 0 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (compress_mem hx)
  have h1 : inner ℂ xi ((E 0 0 * x * E 0 0) xi) = vst x := by
    show inner ℂ xi (E 0 0 (x (E 0 0 xi))) = inner ℂ xi (x xi)
    rw [E00_xi, inner_xi_E00]
  have h2 : inner ℂ xi ((c • E 0 0) xi) = c := by
    show inner ℂ xi (c • E 0 0 xi) = c
    rw [E00_xi, inner_smul_right, inner_xi_xi, mul_one]
  rw [← hc, ← h1, ← hc, h2]

/-! ## Columns -/

theorem E_mul_col (i j : ℕ) {y : Ambient ℂ} (hy : y ∈ closedSubalgebra ℂ)
    (hye : y * E 0 0 = y) : E i j * y = vst (E 0 j * y) • E i 0 := by
  have hm : E 0 j * y ∈ closedSubalgebra ℂ := mul_mem (E_mem 0 j) hy
  calc E i j * y = E i 0 * (E 0 0 * (E 0 j * y) * E 0 0) := by
        rw [mul_assoc (E 0 0), mul_assoc (E 0 j), hye, ← mul_assoc (E 0 0), E_mul_self,
          ← mul_assoc, E_mul_self]
    _ = vst (E 0 j * y) • E i 0 := by
        rw [compress hm, mul_smul_comm, E_mul_self]

/-- **Columns are vectors**: `star y * z = ⟪y ξ, z ξ⟫ • E 0 0`. -/
theorem star_mul_col {y z : Ambient ℂ} (hy : y ∈ closedSubalgebra ℂ) (hye : y * E 0 0 = y)
    (hz : z ∈ closedSubalgebra ℂ) (hze : z * E 0 0 = z) :
    star y * z = inner ℂ (y xi) (z xi) • E 0 0 := by
  have hl : E 0 0 * star y = star y := by
    rw [← star_E 0 0, ← star_mul, hye]
  have hm : star y * z ∈ closedSubalgebra ℂ := mul_mem (star_mem hy) hz
  have hω : vst (star y * z) = inner ℂ (y xi) (z xi) := by
    show inner ℂ xi ((star y) (z xi)) = inner ℂ (y xi) (z xi)
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_right y xi (z xi)
  calc star y * z = E 0 0 * (star y * z) * E 0 0 := by
        rw [← mul_assoc, hl, mul_assoc, hze]
    _ = inner ℂ (y xi) (z xi) • E 0 0 := by rw [compress hm, hω]

/-- An operator killing every `E i 0` kills `𝒦`. -/
theorem mul_eq_zero_of_mul_E {r : Ambient ℂ} (hr : ∀ i, r * E i 0 = 0) {x : Ambient ℂ}
    (hx : x ∈ closedSubalgebra ℂ) : r * x = 0 := by
  have hC : ∀ N, ∀ y ∈ C N, r * y = 0 := by
    intro N y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, j, _, _, rfl⟩ := hy
      rw [← E_mul_self i 0 j, ← mul_assoc, hr i, zero_mul]
    | zero => exact mul_zero r
    | add y z _ _ hy hz => rw [mul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [mul_smul_comm, hy, smul_zero]
  have hsub : (finiteMatrices ℂ : Set (Ambient ℂ)) ⊆ {y | r * y = 0} := by
    intro y hy
    obtain ⟨N, hN⟩ := exists_C hy
    exact hC N y hN
  have hcl : IsClosed {y : Ambient ℂ | r * y = 0} :=
    isClosed_eq (continuous_const_mul r) continuous_const
  have hx' : x ∈ closure (finiteMatrices ℂ : Set (Ambient ℂ)) := hx
  exact closure_minimal hsub hcl hx'

end StabRankAux

end

end GroupApproximation.Full.TWWKK
