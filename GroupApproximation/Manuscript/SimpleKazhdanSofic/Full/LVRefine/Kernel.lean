import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVRefine.Intertwine

/-!
# The refinement homomorphism maps `K₂(n, R)` onto `K₂(n+1, R)`

`simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`), cites Caprace--Rémy for infinite
finitely presented simple Kazhdan groups. On the Leavitt route to that claim, Khanh's Theorem 5.4
(arXiv:2609.08428, tex l.527-556) needs that `D_r : St_n(R) → St_{n+1}(R)` of
`eq:steinberg-refinement` maps the kernel of `St_n(R) → E_n(R)` onto the kernel of
`St_{n+1}(R) → E_{n+1}(R)`.

* `D_r` preserves and reflects `K₂`, through the intertwining identity
  `vecAct_refineHom` and the bijection `splitVec` (`projection_refineHom_eq_one`,
  `projection_eq_one_of_refineHom`).
* For `n ≥ 2` the homomorphism `D_r` is surjective (`refineHom_surjective`). Every generator
  `x_{pq}(b)` of `St_{n+1}(R)` is an image. The two generators joining the split coordinates
  `castSucc r` and `last` are commutators of images, through an auxiliary index `k ≠ r`.

Together these give `map_ker_refineHom`.
-/

namespace GroupApproximation
namespace Full
namespace LVRefine

open SteinbergGroup
open scoped commutatorElement

variable {R : Type*} [Ring R] (L : LeavittFamily R)

section Fixed

variable {n : ℕ} (r : Fin n)

/-- `D_r` maps `K₂(n, R)` into `K₂(n+1, R)` (Khanh Thm 5.4; `sec:questions` l.733-735). -/
theorem projection_refineHom_eq_one {g : SteinbergGroup (Fin n) R} (h : projection g = 1) :
    projection (refineHom L r g) = 1 := by
  refine projection_eq_one_of_vecAct fun w => ?_
  rw [← splitVec_joinVec L r w, vecAct_refineHom, vecAct_eq_of_projection_eq_one h]

/-- `D_r` reflects `K₂`: if `D_r g` lies in `K₂(n+1, R)` then `g` lies in `K₂(n, R)`. -/
theorem projection_eq_one_of_refineHom {g : SteinbergGroup (Fin n) R}
    (h : projection (refineHom L r g) = 1) : projection g = 1 := by
  refine projection_eq_one_of_vecAct fun v => splitVec_injective L r ?_
  rw [← vecAct_refineHom, vecAct_eq_of_projection_eq_one h]

theorem refineHom_row_s0 (j : Fin n) (hrj : r ≠ j) (b : R) :
    refineHom L r (x r j hrj (L.s0 * b)) = x (Fin.castSucc r) (Fin.castSucc j) (cs_ne hrj) b := by
  rw [refineHom_x, refineRoot_of_row L r hrj _ rfl, ← mul_assoc, ← mul_assoc, L.t0_s0, L.t1_s0,
    one_mul, zero_mul, x_zero, mul_one]

theorem refineHom_row_s1 (j : Fin n) (hrj : r ≠ j) (b : R) :
    refineHom L r (x r j hrj (L.s1 * b)) =
      x (Fin.last n) (Fin.castSucc j) (Fin.castSucc_ne_last j).symm b := by
  rw [refineHom_x, refineRoot_of_row L r hrj _ rfl, ← mul_assoc, ← mul_assoc, L.t0_s1, L.t1_s1,
    zero_mul, one_mul, x_zero, one_mul]

theorem refineHom_col_t0 (i : Fin n) (hir : i ≠ r) (b : R) :
    refineHom L r (x i r hir (b * L.t0)) = x (Fin.castSucc i) (Fin.castSucc r) (cs_ne hir) b := by
  rw [refineHom_x, refineRoot_of_col L r hir _ hir rfl, mul_assoc, mul_assoc, L.t0_s0, L.t0_s1,
    mul_one, mul_zero, x_zero, mul_one]

theorem refineHom_col_t1 (i : Fin n) (hir : i ≠ r) (b : R) :
    refineHom L r (x i r hir (b * L.t1)) =
      x (Fin.castSucc i) (Fin.last n) (Fin.castSucc_ne_last i) b := by
  rw [refineHom_x, refineRoot_of_col L r hir _ hir rfl, mul_assoc, mul_assoc, L.t1_s0, L.t1_s1,
    mul_zero, mul_one, x_zero, one_mul]

theorem refineHom_plain {i j : Fin n} (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r) (b : R) :
    refineHom L r (x i j hij b) = x (Fin.castSucc i) (Fin.castSucc j) (cs_ne hij) b := by
  rw [refineHom_x, refineRoot_of_plain L r hij b hir hjr]

/-- The generator `x_{last, r}(b)` is the commutator of the images of `X_{rk}(s1 b)` and
`X_{kr}(t0)`. -/
theorem mem_range_last_self {k : Fin n} (hkr : k ≠ r) (b : R) :
    x (Fin.last n) (Fin.castSucc r) (Fin.castSucc_ne_last r).symm b ∈ (refineHom L r).range := by
  have hrk : r ≠ k := fun e => hkr e.symm
  refine MonoidHom.mem_range.mpr ⟨⁅x r k hrk (L.s1 * b), x k r hkr (1 * L.t0)⁆, ?_⟩
  rw [map_commutatorElement, refineHom_row_s1, refineHom_col_t0,
    x_commutator (Fin.last n) (Fin.castSucc k) (Fin.castSucc r) (Fin.castSucc_ne_last k).symm
      (cs_ne hkr) (Fin.castSucc_ne_last r).symm b 1, mul_one]

/-- The generator `x_{r, last}(b)` is the commutator of the images of `X_{rk}(s0 b)` and
`X_{kr}(t1)`. -/
theorem mem_range_self_last {k : Fin n} (hkr : k ≠ r) (b : R) :
    x (Fin.castSucc r) (Fin.last n) (Fin.castSucc_ne_last r) b ∈ (refineHom L r).range := by
  have hrk : r ≠ k := fun e => hkr e.symm
  refine MonoidHom.mem_range.mpr ⟨⁅x r k hrk (L.s0 * b), x k r hkr (1 * L.t1)⁆, ?_⟩
  rw [map_commutatorElement, refineHom_row_s0, refineHom_col_t1,
    x_commutator (Fin.castSucc r) (Fin.castSucc k) (Fin.last n) (cs_ne hrk)
      (Fin.castSucc_ne_last k) (Fin.castSucc_ne_last r) b 1, mul_one]

/-- Every Steinberg generator of `St_{n+1}(R)` lies in the image of `D_r`, given some `k ≠ r`. -/
theorem x_mem_range {k : Fin n} (hkr : k ≠ r) (p q : Fin (n + 1)) (hpq : p ≠ q) (b : R) :
    x p q hpq b ∈ (refineHom L r).range := by
  induction p using Fin.lastCases with
  | last =>
      induction q using Fin.lastCases with
      | last => exact (hpq rfl).elim
      | cast j =>
          by_cases hj : j = r
          · subst hj
            exact mem_range_last_self L _ hkr b
          · have hrj : r ≠ j := fun e => hj e.symm
            exact MonoidHom.mem_range.mpr ⟨x r j hrj (L.s1 * b), refineHom_row_s1 L r j hrj b⟩
  | cast i =>
      induction q using Fin.lastCases with
      | last =>
          by_cases hi : i = r
          · subst hi
            exact mem_range_self_last L _ hkr b
          · exact MonoidHom.mem_range.mpr ⟨x i r hi (b * L.t1), refineHom_col_t1 L r i hi b⟩
      | cast j =>
          have hij : i ≠ j := fun e => hpq (congrArg Fin.castSucc e)
          by_cases hi : i = r
          · subst hi
            exact MonoidHom.mem_range.mpr ⟨x _ j hij (L.s0 * b), refineHom_row_s0 L _ j hij b⟩
          · by_cases hj : j = r
            · subst hj
              exact MonoidHom.mem_range.mpr ⟨x i _ hij (b * L.t0), refineHom_col_t0 L _ i hij b⟩
            · exact MonoidHom.mem_range.mpr ⟨x i j hij b, refineHom_plain L r hij hi hj b⟩

end Fixed

theorem exists_ne_of_two_le {n : ℕ} (hn : 2 ≤ n) (r : Fin n) : ∃ k : Fin n, k ≠ r := by
  by_cases h : r.val = 0
  · exact ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (show 1 ≠ r.val by omega)⟩
  · exact ⟨⟨0, by omega⟩, Fin.ne_of_val_ne (show 0 ≠ r.val by omega)⟩

/-- For `n ≥ 2` the refinement `D_r : St_n(R) → St_{n+1}(R)` is surjective
(Khanh Thm 5.4; `sec:questions` l.733-735). -/
theorem refineHom_surjective {n : ℕ} (hn : 2 ≤ n) (r : Fin n) :
    Function.Surjective (refineHom L r) := by
  obtain ⟨k, hkr⟩ := exists_ne_of_two_le hn r
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  intro g _
  refine PresentedGroup.generated_by (SteinbergGroup.relations (I := Fin (n + 1)) (R := R))
    (refineHom L r).range ?_ g
  rintro ⟨p, q, hpq, b⟩
  exact x_mem_range L r hkr p q hpq b

/-- Khanh's Theorem 5.4, kernel part: for `n ≥ 2` the refinement `D_r` maps `K₂(n, R)` onto
`K₂(n+1, R)` (`eq:steinberg-refinement`; `sec:questions` l.733-735). -/
theorem map_ker_refineHom {n : ℕ} (hn : 2 ≤ n) (r : Fin n) :
    (SteinbergGroup.projection (I := Fin n) (R := R)).ker.map (refineHom L r) =
      (SteinbergGroup.projection (I := Fin (n + 1)) (R := R)).ker := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro g hg
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    exact projection_refineHom_eq_one L r (MonoidHom.mem_ker.mp hg)
  · intro h hh
    obtain ⟨g, rfl⟩ := refineHom_surjective L hn r h
    exact Subgroup.mem_map_of_mem _
      (MonoidHom.mem_ker.mpr (projection_eq_one_of_refineHom L r (MonoidHom.mem_ker.mp hh)))

end LVRefine
end Full
end GroupApproximation
