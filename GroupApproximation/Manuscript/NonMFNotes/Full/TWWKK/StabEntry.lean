import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.Stab

/-!
# Matrix entries of elements of `𝒦 ⊗ B`

For the spatial model `Stab B ⊆ B(ℓ²(ℕ, H_B))` of the stabilization (`Stab`), we extract the
matrix entries of an element and the truncations to finite corners:

* `Stab.compress B i j x = P_i x P_j`, an operator on `H_B`;
* `Stab.trunc B N = Σ_{k < N} e_{kk} ⊗ 1`, the projection onto the first `N` summands;
* `Stab.finiteSub B`: the operators supported in some finite corner whose compressions lie in
  the image of the faithful representation; it contains the finite matrices;
* `Stab.entry i j x : B`: the `(i, j)` entry of `x ∈ Stab B`, with `rep B (entry i j x) = P_i x P_j`
  (compressions of the closure lie in the closed range of the isometry `rep B`);
* `tendsto_trunc_mul_mul_trunc`: `P_N x P_N → x` for `x ∈ 𝒦 ⊗ B`.

These are the tools for the functoriality `Stab.map` of `𝒦 ⊗ -` (Cuntz, *A new look at
KK-theory*, K-Theory 1 (1987) 31--51, §1; Blackadar, *K-Theory for Operator Algebras*, 17.8).

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-Stab, work order WO-TWWKK-A1).
-/

namespace GroupApproximation.Full.TWWKK

universe u

noncomputable section

open Filter Topology

namespace Stab

variable {B : Type u} [NonUnitalCStarAlgebra B]

/-! ## Compressions -/

variable (B) in
/-- The `(i, j)` compression `x ↦ P_i x P_j` of an operator on `ℓ²(ℕ, H_B)`. -/
def compress (i j : ℕ) : Ambient B →ₗ[ℂ] (RepSpace B →L[ℂ] RepSpace B) where
  toFun x := proj B i ∘L x ∘L inj B j
  map_add' _ _ := ContinuousLinearMap.ext fun _ => rfl
  map_smul' _ _ := ContinuousLinearMap.ext fun _ => rfl

theorem compress_apply (i j : ℕ) (x : Ambient B) (v : RepSpace B) :
    compress B i j x v = x (lp.single 2 j v) i :=
  rfl

theorem continuous_compress (i j : ℕ) : Continuous fun x : Ambient B => compress B i j x :=
  (continuous_const.clm_comp (continuous_id.clm_comp continuous_const) :
    Continuous fun x : Ambient B => proj B i ∘L x ∘L inj B j)

theorem matUnit_compress (i j : ℕ) (x : Ambient B) :
    matUnit B i i 1 * x * matUnit B j j 1 = matUnit B i j (compress B i j x) :=
  ContinuousLinearMap.ext fun _ => rfl

theorem compress_mul_matUnit_mul (i j k : ℕ) (x y : Ambient B) :
    compress B i j (x * matUnit B k k 1 * y) = compress B i k x * compress B k j y :=
  ContinuousLinearMap.ext fun _ => rfl

/-- The compressions of a matrix unit operator. -/
theorem compress_matUnit (i j k l : ℕ) (T : RepSpace B →L[ℂ] RepSpace B) :
    compress B i j (matUnit B k l T) = if i = k ∧ j = l then T else 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  change (lp.single 2 k (T ((lp.single 2 j v : Space B) l)) : Space B) i =
    (if i = k ∧ j = l then T else 0) v
  by_cases hjl : j = l
  · by_cases hik : i = k
    · rw [if_pos (show i = k ∧ j = l from ⟨hik, hjl⟩), hjl, lp.single_apply_self, hik,
        lp.single_apply_self]
    · rw [if_neg (fun h : i = k ∧ j = l => hik h.1), lp.single_apply_ne 2 k _ hik,
        ContinuousLinearMap.zero_apply]
  · rw [if_neg (fun h : i = k ∧ j = l => hjl h.2), lp.single_apply_ne 2 j v (Ne.symm hjl),
      map_zero, lp.single_zero, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply]

theorem compress_matUnit_self (i j : ℕ) (T : RepSpace B →L[ℂ] RepSpace B) :
    compress B i j (matUnit B i j T) = T := by
  rw [compress_matUnit, if_pos (show i = i ∧ j = j from ⟨rfl, rfl⟩)]

theorem matUnit_injective (i j : ℕ) : Function.Injective (matUnit B i j) := fun S T h => by
  have h2 := congrArg (compress B i j) h
  rwa [compress_matUnit_self, compress_matUnit_self] at h2

theorem compress_star (i j : ℕ) (x : Ambient B) :
    compress B i j (star x) = star (compress B j i x) := by
  have h : matUnit B i j (compress B i j (star x)) = matUnit B i j (star (compress B j i x)) := by
    rw [← matUnit_compress, ← star_matUnit, ← matUnit_compress, star_mul, star_mul, star_matUnit,
      star_matUnit, star_one, mul_assoc]
  exact matUnit_injective i j h

/-! ## Truncations -/

variable (B) in
/-- The truncation `P_N = Σ_{k < N} e_{kk} ⊗ 1`, the projection onto the first `N` summands. -/
def trunc (N : ℕ) : Ambient B :=
  ∑ k ∈ Finset.range N, matUnit B k k 1

theorem trunc_mul_matUnit (N i j : ℕ) (T : RepSpace B →L[ℂ] RepSpace B) :
    trunc B N * matUnit B i j T = if i < N then matUnit B i j T else 0 := by
  simp only [trunc, Finset.sum_mul, matUnit_mul_matUnit, one_mul, Finset.sum_ite_eq',
    Finset.mem_range]

theorem matUnit_mul_trunc (N i j : ℕ) (T : RepSpace B →L[ℂ] RepSpace B) :
    matUnit B i j T * trunc B N = if j < N then matUnit B i j T else 0 := by
  simp only [trunc, Finset.mul_sum, matUnit_mul_matUnit, mul_one, Finset.sum_ite_eq,
    Finset.mem_range]

theorem star_trunc (N : ℕ) : star (trunc B N) = trunc B N := by
  simp only [trunc, star_sum, star_matUnit, star_one]

theorem trunc_mul_trunc_of_le {N M : ℕ} (h : N ≤ M) : trunc B M * trunc B N = trunc B N :=
  calc trunc B M * trunc B N = ∑ k ∈ Finset.range N, trunc B M * matUnit B k k 1 :=
        Finset.mul_sum _ _ _
    _ = trunc B N := Finset.sum_congr rfl fun k hk => by
        rw [trunc_mul_matUnit, if_pos (lt_of_lt_of_le (Finset.mem_range.mp hk) h)]

theorem trunc_mul_trunc_of_le' {N M : ℕ} (h : N ≤ M) : trunc B N * trunc B M = trunc B N :=
  calc trunc B N * trunc B M = ∑ k ∈ Finset.range N, matUnit B k k 1 * trunc B M :=
        Finset.sum_mul _ _ _
    _ = trunc B N := Finset.sum_congr rfl fun k hk => by
        rw [matUnit_mul_trunc, if_pos (lt_of_lt_of_le (Finset.mem_range.mp hk) h)]

theorem trunc_mul_self (N : ℕ) : trunc B N * trunc B N = trunc B N :=
  trunc_mul_trunc_of_le le_rfl

theorem trunc_mul_of {N : ℕ} {x : Ambient B} (hx : trunc B N * x * trunc B N = x) :
    trunc B N * x = x :=
  calc trunc B N * x = trunc B N * (trunc B N * x * trunc B N) := by rw [hx]
    _ = trunc B N * trunc B N * x * trunc B N := by simp only [mul_assoc]
    _ = x := by rw [trunc_mul_self, hx]

theorem mul_trunc_of {N : ℕ} {x : Ambient B} (hx : trunc B N * x * trunc B N = x) :
    x * trunc B N = x :=
  calc x * trunc B N = trunc B N * x * trunc B N * trunc B N := by rw [hx]
    _ = trunc B N * x * (trunc B N * trunc B N) := by rw [mul_assoc (trunc B N * x)]
    _ = x := by rw [trunc_mul_self, hx]

theorem trunc_mul_mul_trunc_of_le {N K : ℕ} (h : N ≤ K) {x : Ambient B}
    (hx : trunc B N * x * trunc B N = x) : trunc B K * x * trunc B K = x :=
  calc trunc B K * x * trunc B K = trunc B K * (trunc B N * x * trunc B N) * trunc B K := by
        rw [hx]
    _ = trunc B K * trunc B N * x * (trunc B N * trunc B K) := by simp only [mul_assoc]
    _ = x := by rw [trunc_mul_trunc_of_le h, trunc_mul_trunc_of_le' h, hx]

theorem norm_trunc_le (N : ℕ) : ‖trunc B N‖ ≤ 1 := by
  have h : ‖trunc B N‖ * ‖trunc B N‖ = ‖trunc B N‖ := by
    rw [← CStarRing.norm_star_mul_self, star_trunc, trunc_mul_self]
  nlinarith [norm_nonneg (trunc B N)]

theorem norm_trunc_mul_mul_trunc_le (N : ℕ) (x : Ambient B) :
    ‖trunc B N * x * trunc B N‖ ≤ ‖x‖ := by
  have hp := norm_trunc_le (B := B) N
  have h1 : ‖trunc B N * x * trunc B N‖ ≤ ‖trunc B N * x‖ * ‖trunc B N‖ := norm_mul_le _ _
  have h2 : ‖trunc B N * x‖ ≤ ‖trunc B N‖ * ‖x‖ := norm_mul_le _ _
  have h3 : ‖trunc B N * x‖ * ‖trunc B N‖ ≤ ‖trunc B N * x‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hp
  have h4 : ‖trunc B N‖ * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg _) hp
  linarith

/-- A truncated operator is the finite sum of its matrix entries. -/
theorem trunc_mul_mul_trunc_eq_sum (N : ℕ) (x : Ambient B) :
    trunc B N * x * trunc B N =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, matUnit B i j (compress B i j x) := by
  rw [trunc, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => matUnit_compress i j x

theorem compress_trunc_mul_mul_trunc (N i j : ℕ) (x : Ambient B) :
    compress B i j (trunc B N * x * trunc B N) =
      if i < N ∧ j < N then compress B i j x else 0 := by
  have h : matUnit B i i 1 * (trunc B N * x * trunc B N) * matUnit B j j 1 =
      matUnit B i i 1 * trunc B N * x * (trunc B N * matUnit B j j 1) := by
    simp only [mul_assoc]
  rw [matUnit_compress, matUnit_mul_trunc, trunc_mul_matUnit] at h
  by_cases hi : i < N
  · by_cases hj : j < N
    · rw [if_pos hi, if_pos hj, matUnit_compress] at h
      rw [if_pos (show i < N ∧ j < N from ⟨hi, hj⟩)]
      exact matUnit_injective i j h
    · rw [if_neg hj, mul_zero] at h
      rw [if_neg (fun h' : i < N ∧ j < N => hj h'.2)]
      exact matUnit_injective i j (h.trans (matUnit_zero i j).symm)
  · rw [if_neg hi, zero_mul, zero_mul] at h
    rw [if_neg (fun h' : i < N ∧ j < N => hi h'.1)]
    exact matUnit_injective i j (h.trans (matUnit_zero i j).symm)

/-- The compressions of a product with a truncated left factor are finite sums. -/
theorem compress_mul_of_mul_trunc {N : ℕ} {x : Ambient B} (h : x * trunc B N = x)
    (y : Ambient B) (i j : ℕ) :
    compress B i j (x * y) = ∑ k ∈ Finset.range N, compress B i k x * compress B k j y := by
  conv_lhs => rw [← h]
  rw [trunc, Finset.mul_sum, Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun k _ => compress_mul_matUnit_mul i j k x y

/-! ## Finitely supported operators with entries in `B` -/

variable (B) in
/-- The range of the faithful representation, a `⋆`-subalgebra of `B(H_B)`. -/
def repRange : NonUnitalStarSubalgebra ℂ (RepSpace B →L[ℂ] RepSpace B) :=
  NonUnitalStarAlgHom.range (rep B)

theorem rep_mem_repRange (b : B) : rep B b ∈ repRange B :=
  NonUnitalStarAlgHom.mem_range_self (rep B) b

variable (B) in
theorem isometry_rep : Isometry (rep B) :=
  AddMonoidHomClass.isometry_of_norm (rep B) (norm_rep B)

variable (B) in
theorem isClosed_range_rep : IsClosed (Set.range (rep B)) :=
  (isometry_rep B).isClosedEmbedding.isClosed_range

variable (B) in
/-- The operators supported in a finite corner `P_N x P_N = x` whose compressions all lie in
the range of the faithful representation. -/
def finiteSub : NonUnitalStarSubalgebra ℂ (Ambient B) where
  carrier := {x | ∃ N, trunc B N * x * trunc B N = x ∧ ∀ i j, compress B i j x ∈ repRange B}
  add_mem' := by
    rintro x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    refine ⟨max N M, ?_, fun i j => ?_⟩
    · rw [mul_add, add_mul, trunc_mul_mul_trunc_of_le (le_max_left N M) hN,
        trunc_mul_mul_trunc_of_le (le_max_right N M) hM]
    · rw [map_add]
      exact add_mem (hx i j) (hy i j)
  zero_mem' := ⟨0, by rw [mul_zero, zero_mul], fun i j => by
    rw [map_zero]
    exact zero_mem _⟩
  mul_mem' := by
    rintro x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    have hx' := trunc_mul_mul_trunc_of_le (le_max_left N M) hN
    have hy' := trunc_mul_mul_trunc_of_le (le_max_right N M) hM
    refine ⟨max N M, ?_, fun i j => ?_⟩
    · rw [← mul_assoc, trunc_mul_of hx', mul_assoc, mul_trunc_of hy']
    · rw [compress_mul_of_mul_trunc (mul_trunc_of hN) y i j]
      exact sum_mem fun k _ => mul_mem (hx i k) (hy k j)
  smul_mem' := by
    rintro c x ⟨N, hN, hx⟩
    refine ⟨N, ?_, fun i j => ?_⟩
    · rw [mul_smul_comm, smul_mul_assoc, hN]
    · rw [map_smul]
      exact SMulMemClass.smul_mem c (hx i j)
  star_mem' := by
    rintro x ⟨N, hN, hx⟩
    refine ⟨N, ?_, fun i j => ?_⟩
    · conv_rhs => rw [← hN]
      rw [star_mul, star_mul, star_trunc, mul_assoc]
    · rw [compress_star]
      exact star_mem (hx j i)

theorem mem_finiteSub {x : Ambient B} :
    x ∈ finiteSub B ↔ ∃ N, trunc B N * x * trunc B N = x ∧ ∀ i j, compress B i j x ∈ repRange B :=
  Iff.rfl

theorem generators_subset_finiteSub : generators B ⊆ finiteSub B := by
  rintro x ⟨i, j, b, rfl⟩
  refine mem_finiteSub.mpr ⟨i + j + 1, ?_, fun k l => ?_⟩
  · rw [trunc_mul_matUnit, if_pos (show i < i + j + 1 by omega), matUnit_mul_trunc,
      if_pos (show j < i + j + 1 by omega)]
  · rw [compress_matUnit]
    split_ifs
    · exact rep_mem_repRange b
    · exact zero_mem _

theorem finiteMatrices_le_finiteSub : finiteMatrices B ≤ finiteSub B :=
  NonUnitalStarAlgebra.adjoin_le generators_subset_finiteSub

theorem exists_trunc_of_mem_finiteMatrices {y : Ambient B} (hy : y ∈ finiteMatrices B) :
    ∃ N, trunc B N * y * trunc B N = y :=
  (mem_finiteSub.mp (finiteMatrices_le_finiteSub hy)).imp fun _ h => h.1

/-- The compressions of an element of `𝒦 ⊗ B` lie in the range of the faithful representation. -/
theorem compress_mem_range {x : Ambient B} (hx : x ∈ closedSubalgebra B) (i j : ℕ) :
    compress B i j x ∈ Set.range (rep B) := by
  have hx' : x ∈ closure (finiteMatrices B : Set (Ambient B)) := hx
  have hsub : (finiteMatrices B : Set (Ambient B)) ⊆
      (fun y : Ambient B => compress B i j y) ⁻¹' Set.range (rep B) := by
    intro y hy
    obtain ⟨_, _, hc⟩ := mem_finiteSub.mp (finiteMatrices_le_finiteSub hy)
    exact (NonUnitalStarAlgHom.mem_range (rep B)).mp (hc i j)
  exact closure_minimal hsub ((isClosed_range_rep B).preimage (continuous_compress i j)) hx'

/-- **`P_N x P_N → x`** for every `x ∈ 𝒦 ⊗ B`. -/
theorem tendsto_trunc_mul_mul_trunc {x : Ambient B} (hx : x ∈ closedSubalgebra B) :
    Tendsto (fun N => trunc B N * x * trunc B N) atTop (𝓝 x) := by
  have hx' : x ∈ closure (finiteMatrices B : Set (Ambient B)) := hx
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx' (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := exists_trunc_of_mem_finiteMatrices hy
  refine ⟨N, fun M hM => ?_⟩
  have hyM : trunc B M * y * trunc B M = y := trunc_mul_mul_trunc_of_le hM hN
  have e : trunc B M * x * trunc B M - x = trunc B M * (x - y) * trunc B M + (y - x) := by
    rw [mul_sub, sub_mul, hyM]
    abel
  rw [dist_eq_norm, e]
  have h1 : ‖trunc B M * (x - y) * trunc B M‖ ≤ ‖x - y‖ := norm_trunc_mul_mul_trunc_le M (x - y)
  have h2 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
  have h3 : ‖x - y‖ < ε / 3 := by
    rw [← dist_eq_norm]
    exact hxy
  calc ‖trunc B M * (x - y) * trunc B M + (y - x)‖
        ≤ ‖trunc B M * (x - y) * trunc B M‖ + ‖y - x‖ := norm_add_le _ _
    _ < ε := by linarith

/-! ## Entries -/

/-- **The `(i, j)` entry** of `x ∈ 𝒦 ⊗ B`: the unique `b ∈ B` with `π(b) = P_i x P_j`. -/
def entry (i j : ℕ) (x : Stab B) : B :=
  Classical.choose (Set.mem_range.mp (compress_mem_range x.2 i j))

theorem rep_entry (i j : ℕ) (x : Stab B) : rep B (entry i j x) = compress B i j (x : Ambient B) :=
  Classical.choose_spec (Set.mem_range.mp (compress_mem_range x.2 i j))

theorem entry_add (i j : ℕ) (x y : Stab B) : entry i j (x + y) = entry i j x + entry i j y :=
  rep_injective B <| by
    rw [map_add, rep_entry, rep_entry, rep_entry]
    exact map_add (compress B i j) (x : Ambient B) y

theorem entry_smul (i j : ℕ) (c : ℂ) (x : Stab B) : entry i j (c • x) = c • entry i j x :=
  rep_injective B <| by
    rw [map_smul, rep_entry, rep_entry]
    exact map_smul (compress B i j) c (x : Ambient B)

theorem entry_star (i j : ℕ) (x : Stab B) : entry i j (star x) = star (entry j i x) :=
  rep_injective B <| by
    rw [map_star, rep_entry, rep_entry]
    exact compress_star i j (x : Ambient B)

variable (B) in
/-- The `(i, j)` entry as a linear map `𝒦 ⊗ B → B`. -/
def entryₗ (i j : ℕ) : Stab B →ₗ[ℂ] B where
  toFun := entry i j
  map_add' := entry_add i j
  map_smul' := entry_smul i j

theorem entryₗ_apply (i j : ℕ) (x : Stab B) : entryₗ B i j x = entry i j x :=
  rfl

theorem entry_zero (i j : ℕ) : entry i j (0 : Stab B) = 0 :=
  map_zero (entryₗ B i j)

theorem entry_sub (i j : ℕ) (x y : Stab B) : entry i j (x - y) = entry i j x - entry i j y :=
  map_sub (entryₗ B i j) x y

theorem continuous_entry (i j : ℕ) : Continuous (entry (B := B) i j) := by
  refine (isometry_rep B).isEmbedding.continuous_iff.mpr ?_
  have h : (rep B ∘ entry i j) = fun x : Stab B => compress B i j (x : Ambient B) :=
    funext fun x => rep_entry i j x
  rw [h]
  exact (continuous_compress i j).comp continuous_subtype_val

end Stab

end

end GroupApproximation.Full.TWWKK
