import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZeroCore.Clearing
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZeroCore.Extend

/-!
# Adapted generating families of the column module

Ingredient of `binaryLeavitt_idempotent_dichotomy` (manuscript
`simple_kazhdan_sofic_group.tex`, l.733-735, `sec:questions`, question Q2).

Write `L = L_k(1,2)`.  Fix `e ∈ L` and a length `m`, and index columns by the
binary words `δ` of length `m`.  Columns form a left `L`-module.

* `colSpan k e m` is the left `L`-span of the column `qvec k e m`.
* `colFil k e m n` is the set of columns in `colSpan k e m` whose entries all
  lie in `fil k n`.
* `kappa k m` takes the constant term of every entry.  It is a `k`-linear map
  into the finite-dimensional space `k^{2^m}`.

Main result, by induction on `n`: `colFil k e m n` has a finite family `w` with
two properties.  First, `kappa ∘ w` is `k`-linearly independent.  Second, every
element of `colFil k e m n` is a left `L`-combination of the `w j`.

The step uses the Leavitt relation `s_0 t_0 + s_1 t_1 = 1`.  An element with
vanishing constant terms is `s_0 (t_0 u) + s_1 (t_1 u)`, and each `t_i u`
drops one filtration level.
-/

namespace GroupApproximation.Full.LVLowKZeroCore

open GroupApproximation.BinaryLeavitt

noncomputable section

variable (k : Type) [Field k]

/-- The entrywise constant term of a column. -/
def kappa (m : ℕ) :
    ((Fin m → Fin 2) → BinaryLeavittAlgebra k) →ₗ[k] ((Fin m → Fin 2) → k) where
  toFun v δ := constTerm k (v δ)
  map_add' v w := by
    funext δ
    exact map_add (constTerm k) (v δ) (w δ)
  map_smul' c v := by
    funext δ
    exact map_smul (constTerm k) c (v δ)

theorem kappa_apply (m : ℕ) (v : (Fin m → Fin 2) → BinaryLeavittAlgebra k)
    (δ : Fin m → Fin 2) : kappa k m v δ = constTerm k (v δ) := rfl

/-- The left `L`-span of the column `qvec k e m`. -/
def colSpan (e : BinaryLeavittAlgebra k) (m : ℕ) :
    Submodule (BinaryLeavittAlgebra k) ((Fin m → Fin 2) → BinaryLeavittAlgebra k) :=
  Submodule.span (BinaryLeavittAlgebra k) {qvec k e m}

/-- Columns of `colSpan k e m` with all entries in `fil k n`. -/
def colFil (e : BinaryLeavittAlgebra k) (m n : ℕ) :
    Set ((Fin m → Fin 2) → BinaryLeavittAlgebra k) :=
  {v | v ∈ colSpan k e m ∧ ∀ δ, v δ ∈ fil k n}

theorem mem_colFil {e : BinaryLeavittAlgebra k} {m n : ℕ}
    {v : (Fin m → Fin 2) → BinaryLeavittAlgebra k} :
    v ∈ colFil k e m n ↔ v ∈ colSpan k e m ∧ ∀ δ, v δ ∈ fil k n := Iff.rfl

theorem colFil_mono {e : BinaryLeavittAlgebra k} {m n n' : ℕ} (h : n ≤ n') :
    colFil k e m n ⊆ colFil k e m n' := by
  intro v hv
  exact (mem_colFil k).mpr
    ⟨((mem_colFil k).mp hv).1, fun δ => fil_mono k h (((mem_colFil k).mp hv).2 δ)⟩

theorem eq_zero_of_mem_colFil_zero {e : BinaryLeavittAlgebra k} {m : ℕ}
    {v : (Fin m → Fin 2) → BinaryLeavittAlgebra k} (hv : v ∈ colFil k e m 0) : v = 0 := by
  funext δ
  exact eq_zero_of_mem_fil_zero k (((mem_colFil k).mp hv).2 δ)

/-- With clearing bounds `(m, N)` for `e`, the column `qvec k e m` lies in
`colFil k e m (N + m)`. -/
theorem qvec_mem_colFil {e : BinaryLeavittAlgebra k} {m N : ℕ}
    (h : ∀ δ : List (Fin 2), m ≤ δ.length → e * (family k).wordS δ ∈ fil k (N + δ.length)) :
    qvec k e m ∈ colFil k e m (N + m) :=
  (mem_colFil k).mpr ⟨Submodule.mem_span_singleton_self _, qvec_mem_fil k h⟩

/-- **Adapted generators.**  At every filtration level, `colFil k e m n` has a
finite family, independent modulo constant terms, that generates it over
`L`. -/
theorem exists_adapted_generators (e : BinaryLeavittAlgebra k) (m n : ℕ) :
    ∃ (r : ℕ) (w : Fin r → ((Fin m → Fin 2) → BinaryLeavittAlgebra k)),
      (∀ j, w j ∈ colFil k e m n) ∧ LinearIndependent k (kappa k m ∘ w) ∧
        ∀ v ∈ colFil k e m n, v ∈ Submodule.span (BinaryLeavittAlgebra k) (Set.range w) := by
  induction n with
  | zero =>
      refine ⟨0, fun j => j.elim0, fun j => j.elim0, linearIndependent_empty_type, ?_⟩
      intro v hv
      rw [eq_zero_of_mem_colFil_zero k hv]
      exact Submodule.zero_mem _
  | succ n ih =>
      obtain ⟨r, w, hwM, hwli, hwspan⟩ := ih
      obtain ⟨r', w', hw'M, hsub, hli', hspan⟩ :=
        exists_adapted_extension (kappa k m) (colFil k e m (n + 1)) w
          (fun j => colFil_mono k (Nat.le_succ n) (hwM j)) hwli
      refine ⟨r', w', hw'M, hli', fun u hu => ?_⟩
      have hrange : Set.range w ⊆ Set.range w' := by
        rintro _ ⟨j, rfl⟩
        obtain ⟨j', hj'⟩ := hsub j
        exact ⟨j', hj'⟩
      have hle : Submodule.span (BinaryLeavittAlgebra k) (Set.range w) ≤
          Submodule.span (BinaryLeavittAlgebra k) (Set.range w') :=
        Submodule.span_mono hrange
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (hspan u hu)
      -- `u' = u - ∑ c j • w' j` has vanishing constant terms.
      have hκ : kappa k m (u - ∑ j, c j • w' j) = 0 := by
        rw [map_sub, map_sum, ← hc, sub_eq_zero]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Function.comp_apply]
      have hu'M : u - ∑ j, c j • w' j ∈ colFil k e m (n + 1) := by
        refine (mem_colFil k).mpr ⟨?_, fun δ => ?_⟩
        · refine Submodule.sub_mem _ ((mem_colFil k).mp hu).1
            (Submodule.sum_mem _ fun j _ => ?_)
          exact Submodule.smul_of_tower_mem _ (c j) ((mem_colFil k).mp (hw'M j)).1
        · rw [Pi.sub_apply, Finset.sum_apply]
          refine Submodule.sub_mem _ (((mem_colFil k).mp hu).2 δ)
            (Submodule.sum_mem _ fun j _ => ?_)
          rw [Pi.smul_apply]
          exact Submodule.smul_mem _ (c j) (((mem_colFil k).mp (hw'M j)).2 δ)
      have hpos : ∀ δ, (u - ∑ j, c j • w' j) δ ∈ pos k (n + 1) := by
        intro δ
        have h := sub_constTerm_mem_pos k (((mem_colFil k).mp hu'M).2 δ)
        rwa [← kappa_apply k m (u - ∑ j, c j • w' j) δ, hκ, Pi.zero_apply, zero_smul,
          sub_zero] at h
      -- Each `t_i • u'` drops to level `n`, hence is generated by `w`.
      have ht : ∀ i : Fin 2, (family k).t i • (u - ∑ j, c j • w' j) ∈
          Submodule.span (BinaryLeavittAlgebra k) (Set.range w') := by
        intro i
        refine hle (hwspan _ ((mem_colFil k).mpr ⟨?_, fun δ => ?_⟩))
        · exact Submodule.smul_mem _ _ ((mem_colFil k).mp hu'M).1
        · rw [Pi.smul_apply, smul_eq_mul]
          exact t_mul_mem_fil k (hpos δ) i
      have hu'span : u - ∑ j, c j • w' j ∈
          Submodule.span (BinaryLeavittAlgebra k) (Set.range w') := by
        have hdecomp : u - ∑ j, c j • w' j =
            (family k).s 0 • ((family k).t 0 • (u - ∑ j, c j • w' j)) +
              (family k).s 1 • ((family k).t 1 • (u - ∑ j, c j • w' j)) := by
          rw [smul_smul, smul_smul, ← add_smul, (family k).sum_s_mul_t, one_smul]
        rw [hdecomp]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (ht 0))
          (Submodule.smul_mem _ _ (ht 1))
      have hsum : ∑ j, c j • w' j ∈ Submodule.span (BinaryLeavittAlgebra k) (Set.range w') :=
        Submodule.sum_mem _ fun j _ =>
          Submodule.smul_of_tower_mem _ (c j) (Submodule.subset_span ⟨j, rfl⟩)
      have h := Submodule.add_mem _ hu'span hsum
      rwa [sub_add_cancel] at h

end

end GroupApproximation.Full.LVLowKZeroCore
