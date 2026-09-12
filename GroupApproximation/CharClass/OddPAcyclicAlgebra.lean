import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.NoncommRing

/-!
# The telescoping contraction of a tensor power, as ring algebra

Lane `lix-cupone`, block `OddPAcyclic*` of `lix-steenrod`'s plan (§3.4, route (A)).

Let `C` be a complex with a homotopy `s` from the identity to a chain map `e` concentrated in degree
`0`: `d s + s d = 1 - e`, `d e = 0`, `e d = 0`.  On the `r`-fold tensor power the standard
homotopy from the identity to `e^{⊗r}` is

```text
S = s ⊗ 1^{⊗(r-1)} + e ⊗ (s ⊗ 1^{⊗(r-2)} + e ⊗ (⋯))         (recursively, slot 0 first)
  = Σ_j e^{⊗j} ⊗ s ⊗ 1^{⊗(r-j-1)}                           (flat)
```

and `d S + S d = 1 - e^{⊗r}`.  This file proves that identity once, in an arbitrary ring, from the
five relations the slot operators satisfy, so that the tuple model only has to check relations
between two slot operators at a time.  With `D j`, `T j`, `E j` the slot-`j` boundary, contraction
and projection:

* `D j T j + T j D j = 1 - E j`   (the one-slot contraction);
* `D l T j + T j D l = 0` for `j ≠ l`   (two odd operators on different slots anticommute);
* `D l E j = E j D l` for `j ≠ l`   (an even operator commutes);
* `D j E j = 0` and `E j D j = 0`   (`e` lands in degree `0` and kills boundaries).

The contraction is defined recursively (`contrOp`), which is the two-factor formula iterated, so the
proof is an induction on `r` with no noncommutative products to reorder.  Model-tested on the
chains of the 2-simplex at `r = 1, 2, 3` with two different contraction data
(`backup/lix-cupone/oddp_acyclic_signs.py`, `OVERALL: GREEN`).

The two module-level facts the assembly needs are here too: `eAll` kills a submodule as soon as one
member kills it and the others preserve it, and `contrOp` raises a grading by one when every `T`
does and every `E` preserves it.
-/

namespace GroupApproximation.CharClass

namespace OddPAcyclic

variable {R : Type*} [Ring R]

/-- **The recursive contraction**: `T 0 + E 0 * (the contraction of the remaining slots)`. -/
def contrOp : ∀ {r : ℕ}, (Fin r → R) → (Fin r → R) → R
  | 0, _, _ => 0
  | _ + 1, T, E => T 0 + E 0 * contrOp (fun i => T i.succ) (fun i => E i.succ)

/-- The product `E 0 * E 1 * ⋯ * E (r-1)`, right-nested, `1` at `r = 0`. -/
def eAll : ∀ {r : ℕ}, (Fin r → R) → R
  | 0, _ => 1
  | _ + 1, E => E 0 * eAll (fun i => E i.succ)

theorem contrOp_zero (T E : Fin 0 → R) : contrOp T E = 0 := rfl

theorem contrOp_succ {r : ℕ} (T E : Fin (r + 1) → R) :
    contrOp T E = T 0 + E 0 * contrOp (fun i => T i.succ) (fun i => E i.succ) := rfl

theorem eAll_zero (E : Fin 0 → R) : eAll E = 1 := rfl

theorem eAll_succ {r : ℕ} (E : Fin (r + 1) → R) : eAll E = E 0 * eAll (fun i => E i.succ) := rfl

/-- An element anticommuting with every `T` and commuting with every `E` anticommutes with the
contraction. -/
theorem anticomm_contrOp (x : R) :
    ∀ {r : ℕ} (T E : Fin r → R), (∀ i, x * T i + T i * x = 0) → (∀ i, x * E i = E i * x) →
      x * contrOp T E + contrOp T E * x = 0
  | 0, T, E, _, _ => by rw [contrOp_zero, mul_zero, zero_mul, add_zero]
  | r + 1, T, E, hT, hE => by
    have ih := anticomm_contrOp x (fun i : Fin r => T i.succ) (fun i => E i.succ)
      (fun i => hT i.succ) (fun i => hE i.succ)
    have hx0 : x * E 0 - E 0 * x = 0 := sub_eq_zero.mpr (hE 0)
    rw [contrOp_succ]
    have key : x * (T 0 + E 0 * contrOp (fun i => T i.succ) (fun i => E i.succ))
        + (T 0 + E 0 * contrOp (fun i => T i.succ) (fun i => E i.succ)) * x
        = (x * T 0 + T 0 * x)
          + (x * E 0 - E 0 * x) * contrOp (fun i => T i.succ) (fun i => E i.succ)
          + E 0 * (x * contrOp (fun i => T i.succ) (fun i => E i.succ)
            + contrOp (fun i => T i.succ) (fun i => E i.succ) * x) := by
      noncomm_ring
    rw [key, hT 0, hx0, ih, zero_mul, mul_zero, add_zero, add_zero]

/-- **The telescoping identity**: `d S + S d = 1 - E 0 * ⋯ * E (r-1)` with `d = Σ_j D j`. -/
theorem sum_mul_contrOp_add :
    ∀ {r : ℕ} (D T E : Fin r → R),
      (∀ j, D j * T j + T j * D j = 1 - E j) →
      (∀ j l, j ≠ l → D l * T j + T j * D l = 0) →
      (∀ j l, j ≠ l → D l * E j = E j * D l) →
      (∀ j, D j * E j = 0) → (∀ j, E j * D j = 0) →
      (∑ j, D j) * contrOp T E + contrOp T E * (∑ j, D j) = 1 - eAll E
  | 0, D, T, E, _, _, _, _, _ => by
    rw [contrOp_zero, eAll_zero, mul_zero, zero_mul, add_zero, sub_self]
  | r + 1, D, T, E, H1, H2, H3, H4, H5 => by
    have ih : (∑ i : Fin r, D i.succ) * contrOp (fun i : Fin r => T i.succ) (fun i => E i.succ)
        + contrOp (fun i : Fin r => T i.succ) (fun i => E i.succ) * (∑ i : Fin r, D i.succ)
        = 1 - eAll (fun i : Fin r => E i.succ) :=
      sum_mul_contrOp_add (fun i : Fin r => D i.succ) (fun i => T i.succ) (fun i => E i.succ)
        (fun j => H1 j.succ)
        (fun j l hjl => H2 j.succ l.succ (fun h => hjl (Fin.succ_inj.mp h)))
        (fun j l hjl => H3 j.succ l.succ (fun h => hjl (Fin.succ_inj.mp h)))
        (fun j => H4 j.succ) (fun j => H5 j.succ)
    have hDT : (∑ i : Fin r, D i.succ) * T 0 + T 0 * (∑ i : Fin r, D i.succ) = 0 := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => H2 0 i.succ (Fin.succ_ne_zero i).symm
    have hDE : (∑ i : Fin r, D i.succ) * E 0 - E 0 * (∑ i : Fin r, D i.succ) = 0 := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_eq_zero fun i _ => sub_eq_zero.mpr (H3 0 i.succ (Fin.succ_ne_zero i).symm)
    have hD0S : D 0 * contrOp (fun i : Fin r => T i.succ) (fun i => E i.succ)
        + contrOp (fun i : Fin r => T i.succ) (fun i => E i.succ) * D 0 = 0 :=
      anticomm_contrOp (D 0) (fun i : Fin r => T i.succ) (fun i => E i.succ)
        (fun i => H2 i.succ 0 (Fin.succ_ne_zero i)) (fun i => H3 i.succ 0 (Fin.succ_ne_zero i))
    rw [Fin.sum_univ_succ, contrOp_succ, eAll_succ]
    generalize (∑ i : Fin r, D i.succ) = d' at ih hDT hDE ⊢
    generalize contrOp (fun i : Fin r => T i.succ) (fun i => E i.succ) = S' at ih hD0S ⊢
    generalize eAll (fun i : Fin r => E i.succ) = EA at ih ⊢
    have key : (D 0 + d') * (T 0 + E 0 * S') + (T 0 + E 0 * S') * (D 0 + d')
        = (D 0 * T 0 + T 0 * D 0) + (d' * T 0 + T 0 * d') + (D 0 * E 0) * S'
          + E 0 * (D 0 * S' + S' * D 0) - (E 0 * D 0) * S'
          + (d' * E 0 - E 0 * d') * S' + E 0 * (d' * S' + S' * d') := by
      noncomm_ring
    rw [key, H1 0, hDT, H4 0, hD0S, H5 0, hDE, ih]
    noncomm_ring

/-! ## Two module-level facts -/

section Module

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- If every member preserves a submodule, so does `eAll`. -/
theorem eAll_mem :
    ∀ {r : ℕ} (E : Fin r → Module.End K M) (V : Submodule K M),
      (∀ l, ∀ v ∈ V, E l v ∈ V) → ∀ v ∈ V, eAll E v ∈ V
  | 0, _, _, _, v, hv => hv
  | r + 1, E, V, hE, v, hv => by
    rw [eAll_succ, Module.End.mul_apply]
    exact hE 0 _ (eAll_mem (fun i : Fin r => E i.succ) V (fun l => hE l.succ) v hv)

/-- **`eAll` kills a submodule** that one member kills and every other member preserves. -/
theorem eAll_eq_zero :
    ∀ {r : ℕ} (E : Fin r → Module.End K M) (V : Submodule K M) (j : Fin r),
      (∀ v ∈ V, E j v = 0) → (∀ l, l ≠ j → ∀ v ∈ V, E l v ∈ V) → ∀ v ∈ V, eAll E v = 0
  | 0, _, _, j, _, _, _, _ => j.elim0
  | r + 1, E, V, j, hj, hl, v, hv => by
    rw [eAll_succ, Module.End.mul_apply]
    induction j using Fin.cases with
    | zero =>
      exact hj _ (eAll_mem (fun i : Fin r => E i.succ) V
        (fun l => hl l.succ (Fin.succ_ne_zero l)) v hv)
    | succ j' =>
      rw [eAll_eq_zero (fun i : Fin r => E i.succ) V j' hj
        (fun l hlj => hl l.succ (fun h => hlj (Fin.succ_inj.mp h))) v hv, map_zero]

/-- **The contraction raises a grading by one** when every `T` does and every `E` preserves it. -/
theorem contrOp_mem (W : ℕ → Submodule K M) :
    ∀ {r : ℕ} (T E : Fin r → Module.End K M),
      (∀ i m, ∀ v ∈ W m, T i v ∈ W (m + 1)) → (∀ i m, ∀ v ∈ W m, E i v ∈ W m) →
      ∀ m, ∀ v ∈ W m, contrOp T E v ∈ W (m + 1)
  | 0, _, _, _, _, m, v, _ => by
    rw [contrOp_zero, LinearMap.zero_apply]
    exact (W (m + 1)).zero_mem
  | r + 1, T, E, hT, hE, m, v, hv => by
    rw [contrOp_succ, LinearMap.add_apply, Module.End.mul_apply]
    exact (W (m + 1)).add_mem (hT 0 m v hv)
      (hE 0 (m + 1) _ (contrOp_mem W (fun i : Fin r => T i.succ) (fun i => E i.succ)
        (fun i => hT i.succ) (fun i => hE i.succ) m v hv))

end Module

end OddPAcyclic

end GroupApproximation.CharClass
