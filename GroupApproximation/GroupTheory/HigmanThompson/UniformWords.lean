import GroupApproximation.GroupTheory.HigmanThompson.BrownPresentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Uniform subdivisions as positive words

In Brown's model a positive word is a sequence of subdivisions of the unit grid of the half
line: `x_k` cuts the unit interval `[k, k+1]` into `n = m + 2` equal pieces and renumbers
the grid.  This module writes down three explicit families of positive words and computes
their evaluations exactly, point by point:

* `vword k c = [k+c-1, …, k]` cuts each of the `c` unit intervals `[k, k+c]` into `n`
  pieces: it is `t ↦ k + n (t - k)` on `[k, k+c]` (`vword_apply`);
* `uword k d` cuts `[k, k+1]` uniformly to depth `d`: it is `t ↦ k + n^d (t - k)` on
  `[k, k+1]` (`uword_apply`);
* `wword k ds` cuts the unit intervals `[k+j, k+j+1]` uniformly to the depths `ds[j]`
  (`wword_apply`), so it sends `[k+j, k+j+1]` linearly onto
  `[k + psum j, k + psum j + n^{ds[j]}]`.

These are what the generation theorem needs: a geometric element of `F_{n,∞}`,
conjugated by uniform subdivisions of large depth, becomes exactly a `wword`.
-/

namespace GroupApproximation
namespace HigmanThompson

variable (m : ℕ)

/-- The evaluation of a positive word, head applied first. -/
noncomputable def posMap (l : List ℕ) : Equiv.Perm ℚ := brownEval m (brownPos m l)

theorem posMap_cons (i : ℕ) (l : List ℕ) : posMap m (i :: l) = posMap m l * xg m i :=
  brownEval_pos_cons m i l

theorem posMap_append (l₁ l₂ : List ℕ) : posMap m (l₁ ++ l₂) = posMap m l₂ * posMap m l₁ := by
  rw [posMap, brownPos_append, map_mul]
  rfl

theorem posMap_mem_brownF (l : List ℕ) : posMap m l ∈ brownF m := ⟨brownPos m l, rfl⟩

/-! ## `vword` -/

/-- `[k + c - 1, …, k]`. -/
def vword (k : ℕ) : ℕ → List ℕ
  | 0 => []
  | c + 1 => (k + c) :: vword k c

theorem vword_apply (k c : ℕ) (t : ℚ) :
    (t ≤ k → posMap m (vword k c) t = t) ∧
    ((k : ℚ) ≤ t → t ≤ k + c → posMap m (vword k c) t = k + ((m : ℚ) + 2) * (t - k)) ∧
    ((k : ℚ) + c ≤ t → posMap m (vword k c) t = t + c * ((m : ℚ) + 1)) := by
  have hm0 : (0 : ℚ) ≤ (m : ℚ) := by positivity
  induction c generalizing t with
  | zero =>
    refine ⟨fun _ => rfl, fun h1 h2 => ?_, fun _ => ?_⟩
    · have ht : t = k := le_antisymm (by simpa using h2) h1
      show t = _
      rw [ht]
      ring
    · show t = _
      simp
  | succ c ih =>
    have hcast : ((k + c : ℕ) : ℚ) = (k : ℚ) + c := by push_cast; ring
    refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h3 => ?_⟩
    · rw [vword, posMap_cons, Equiv.Perm.mul_apply,
        xg_fix (show t ≤ ((k + c : ℕ) : ℚ) by rw [hcast]; linarith [(Nat.cast_nonneg c : (0 : ℚ) ≤ c)])]
      exact (ih t).1 h1
    · rw [vword, posMap_cons, Equiv.Perm.mul_apply]
      rcases le_or_gt t ((k : ℚ) + c) with h4 | h4
      · rw [xg_fix (show t ≤ ((k + c : ℕ) : ℚ) by rw [hcast]; exact h4)]
        exact (ih t).2.1 h1 h4
      · have h2' : t ≤ ((k + c : ℕ) : ℚ) + 1 := by push_cast at h2 ⊢; linarith
        rw [xg_apply, xfun_of_mem (show ((k + c : ℕ) : ℚ) ≤ t by rw [hcast]; exact h4.le) h2',
          (ih _).2.2 (by rw [hcast]; nlinarith), hcast]
        ring
    · rw [vword, posMap_cons, Equiv.Perm.mul_apply,
        xg_apply, xfun_of_ge (show ((k + c : ℕ) : ℚ) + 1 ≤ t by push_cast at h3 ⊢; linarith),
        (ih _).2.2 (by push_cast at h3 ⊢; linarith)]
      push_cast
      ring

/-! ## `uword` -/

/-- Uniform subdivision of `[k, k+1]` to depth `d`. -/
def uword (k : ℕ) : ℕ → List ℕ
  | 0 => []
  | d + 1 => uword k d ++ vword k ((m + 2) ^ d)

theorem uword_apply (k d : ℕ) (t : ℚ) :
    (t ≤ k → posMap m (uword m k d) t = t) ∧
    ((k : ℚ) ≤ t → t ≤ k + 1 → posMap m (uword m k d) t = k + ((m : ℚ) + 2) ^ d * (t - k)) ∧
    ((k : ℚ) + 1 ≤ t → posMap m (uword m k d) t = t + (((m : ℚ) + 2) ^ d - 1)) := by
  have hm : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  induction d generalizing t with
  | zero =>
    refine ⟨fun _ => rfl, fun _ _ => ?_, fun _ => ?_⟩
    · show t = _
      ring
    · show t = _
      ring
  | succ d ih =>
    have hpow : (((m + 2) ^ d : ℕ) : ℚ) = ((m : ℚ) + 2) ^ d := by push_cast; ring
    have hpd : (0 : ℚ) < ((m : ℚ) + 2) ^ d := pow_pos hm d
    refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h3 => ?_⟩
    · rw [uword, posMap_append, Equiv.Perm.mul_apply, (ih t).1 h1]
      exact (vword_apply m k _ t).1 h1
    · rw [uword, posMap_append, Equiv.Perm.mul_apply, (ih t).2.1 h1 h2,
        (vword_apply m k _ _).2.1 (by nlinarith) (by rw [hpow]; nlinarith)]
      ring
    · rw [uword, posMap_append, Equiv.Perm.mul_apply, (ih t).2.2 h3,
        (vword_apply m k _ _).2.2 (by rw [hpow]; linarith), hpow]
      ring

/-! ## `wword` -/

/-- Prefix sums of `n^{ds[i]}`. -/
def psum : List ℕ → ℕ → ℕ
  | [], _ => 0
  | _ :: _, 0 => 0
  | d :: ds, j + 1 => (m + 2) ^ d + psum ds j

/-- The total `∑ n^{ds[i]}`. -/
def tot : List ℕ → ℕ
  | [] => 0
  | d :: ds => (m + 2) ^ d + tot ds

theorem length_le_tot (ds : List ℕ) : ds.length ≤ tot m ds := by
  induction ds with
  | nil => simp [tot]
  | cons d ds ih =>
    have h : 1 ≤ (m + 2) ^ d := Nat.one_le_pow _ _ (by omega)
    simp only [List.length_cons, tot]
    omega

/-- Uniform subdivision of the unit intervals `[k+j, k+j+1]` to depths `ds[j]`. -/
def wword (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: ds => wword (k + 1) ds ++ uword m k d

theorem wword_apply (ds : List ℕ) (k : ℕ) (t : ℚ) :
    (t ≤ k → posMap m (wword m k ds) t = t) ∧
    (∀ j : ℕ, j < ds.length → (k : ℚ) + j ≤ t → t ≤ k + j + 1 →
      posMap m (wword m k ds) t =
        k + psum m ds j + ((m : ℚ) + 2) ^ (ds.getD j 0) * (t - (k + j))) ∧
    ((k : ℚ) + ds.length ≤ t →
      posMap m (wword m k ds) t = t + ((tot m ds : ℚ) - ds.length)) := by
  have hm : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  induction ds generalizing k t with
  | nil =>
    refine ⟨fun _ => rfl, fun j hj => absurd hj (by simp), fun _ => ?_⟩
    show t = _
    simp [tot]
  | cons d ds ih =>
    have hlen := length_le_tot m ds
    have hlenQ : (ds.length : ℚ) ≤ tot m ds := by exact_mod_cast hlen
    refine ⟨fun h1 => ?_, fun j hj h1 h2 => ?_, fun h3 => ?_⟩
    · rw [wword, posMap_append, Equiv.Perm.mul_apply,
        (ih (k + 1) t).1 (by push_cast; linarith)]
      exact (uword_apply m k d t).1 h1
    · rw [wword, posMap_append, Equiv.Perm.mul_apply]
      rcases j with _ | j
      · rw [(ih (k + 1) t).1 (by push_cast at h2 ⊢; linarith),
          (uword_apply m k d t).2.1 (by simpa using h1) (by simpa using h2)]
        simp [psum]
      · have hj' : j < ds.length := by simpa using hj
        have hw := (ih (k + 1) t).2.1 j hj' (by push_cast at h1 ⊢; linarith)
          (by push_cast at h2 ⊢; linarith)
        have hpj : (0 : ℚ) ≤ ((m : ℚ) + 2) ^ (ds.getD j 0) := (pow_pos hm _).le
        have hge : ((k : ℚ) + 1) ≤ posMap m (wword m (k + 1) ds) t := by
          rw [hw]
          have h0 : (0 : ℚ) ≤ t - ((k : ℚ) + 1 + j) := by push_cast at h1; linarith
          have h00 : (0 : ℚ) ≤ (psum m ds j : ℚ) := Nat.cast_nonneg _
          have hprod := mul_nonneg hpj h0
          push_cast
          linarith
        rw [(uword_apply m k d _).2.2 hge, hw]
        simp only [psum, List.getD_cons_succ]
        push_cast
        ring
    · have h3' : ((k + 1 : ℕ) : ℚ) + ds.length ≤ t := by
        simp only [List.length_cons] at h3
        push_cast at h3 ⊢
        linarith
      have hw := (ih (k + 1) t).2.2 h3'
      have hge : ((k : ℚ) + 1) ≤ posMap m (wword m (k + 1) ds) t := by
        rw [hw]
        push_cast at h3'
        linarith
      rw [wword, posMap_append, Equiv.Perm.mul_apply, (uword_apply m k d _).2.2 hge, hw]
      simp only [tot, List.length_cons]
      push_cast
      ring

#audit_axioms GroupApproximation.HigmanThompson.wword_apply

end HigmanThompson
end GroupApproximation
