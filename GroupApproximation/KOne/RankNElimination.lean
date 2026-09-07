import GroupApproximation.PropertyTT.BoundedGeneration

/-!
# Gaussian elimination at every rank over a strongly divisible ring

`Leavitt/MatrixDiagonalization.lean` proves the GE property at rank two: over a
nontrivial ring in which every nonzero element divides the identity on both
sides, elementary row and column operations carry every invertible `2 × 2`
matrix to `diag(u, 1)`.  `PropertyTT/CoordinateBlocks.lean` proves the
*one-stage* version at every rank: for two distinct coordinates `i ≠ j`,
elementary operations isolate `j` as an identity summand.  Neither iterates.
This file iterates, and reaches the diagonal:

> for every `A ∈ GL_ι(R)` and every `l : ι` there are `E, F ∈ EL_ι(R)` and a
> unit `u` of `R` with `E · A · F = diagAt l u`,

where `diagAt l u` carries `u` at `l` and `1` everywhere else.

This is the elementary reduction of Menal and Moncasi in the shape Ara,
Goodearl and Pardo use it: `non_mf_groups_exist.tex` cites it as "the
elementary reduction of Menal and Moncasi~\cite[proof of Theorem~2.2, and the
Remark after Corollary~2.3]{MenalMoncasi}" in the proof of
`thm:mf-quotient-units`, and it is the missing ingredient of the Khanh--Thanh
input of `cor:leavitt-mf-quotient`.

## What this file does not do

It does not identify the surviving unit `u`, and it says nothing about which
units can occur: that is the `K₁` computation, not the elimination.  It also
proves nothing about word length --- `PropertyTT/BoundedGeneration.lean` is
where uniform width lives, and the iteration below deliberately drops the list
bookkeeping that file carries.

## Why the one-stage theorem is not enough by itself

`exists_coordinateBlock_reduction` clears one coordinate, but its statement
does not say *which* elementary indices its moves use, so nothing in it
prevents a second application from destroying the first one's work.  The
iteration therefore needs a step that carries an invariant.  `ClearedOn S A`
--- `A` lies in `coordinateBlock R j` for every `j ∈ S` --- is that invariant,
and it is preserved for free: an elementary matrix whose two indices avoid `q`
lies in `coordinateBlock R q` (`elementaryUnit_mem_coordinateBlock_of_ne`),
and coordinate blocks are subgroups.  Only two moves have to be written out by
hand, and only their effect on the single entry `(t, t)` is computed; the
simultaneous row and column clearing is `rightClearFactors` and
`leftClearFactors` of `PropertyTT`, unchanged.

The pivot index is always the surviving index `l`, so `l` is never cleared and
no lower bound on the rank is needed.
-/

namespace GroupApproximation
namespace RankNElimination

open scoped BigOperators

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

/-! ### Reachability by elementary moves -/

/-- `M` is reached from `A` by elementary row and column operations. -/
def Reaches (A M : (Matrix ι ι R)ˣ) : Prop :=
  ∃ E ∈ elementaryGroup ι R, ∃ F ∈ elementaryGroup ι R, M = E * A * F

theorem Reaches.refl (A : (Matrix ι ι R)ˣ) : Reaches A A :=
  ⟨1, one_mem _, 1, one_mem _, by group⟩

theorem Reaches.trans {A M N : (Matrix ι ι R)ˣ} (h : Reaches A M)
    (h' : Reaches M N) : Reaches A N := by
  obtain ⟨E, hE, F, hF, hM⟩ := h
  obtain ⟨E', hE', F', hF', hN⟩ := h'
  refine ⟨E' * E, mul_mem hE' hE, F * F', mul_mem hF hF', ?_⟩
  rw [hN, hM]
  group

theorem Reaches.left {A E : (Matrix ι ι R)ˣ} (hE : E ∈ elementaryGroup ι R) :
    Reaches A (E * A) :=
  ⟨E, hE, 1, one_mem _, by group⟩

theorem Reaches.right {A F : (Matrix ι ι R)ˣ} (hF : F ∈ elementaryGroup ι R) :
    Reaches A (A * F) :=
  ⟨1, one_mem _, F, hF, by group⟩

/-! ### The cleared invariant -/

/-- `A` is *cleared on* `S`: every index of `S` is already an identity summand
of `A`.  This is a conjunction of the landed memberships `A ∈ coordinateBlock
R j`, so all the closure properties are subgroup properties. -/
def ClearedOn (S : Finset ι) (A : (Matrix ι ι R)ˣ) : Prop :=
  ∀ j ∈ S, A ∈ coordinateBlock R j

theorem clearedOn_empty (A : (Matrix ι ι R)ˣ) : ClearedOn ∅ A := fun j hj ↦
  absurd hj (Finset.notMem_empty j)

theorem ClearedOn.mono {S T : Finset ι} {A : (Matrix ι ι R)ˣ}
    (h : ClearedOn S A) (hTS : T ⊆ S) : ClearedOn T A := fun j hj ↦ h j (hTS hj)

theorem ClearedOn.row {S : Finset ι} {A : (Matrix ι ι R)ˣ} (h : ClearedOn S A)
    {j : ι} (hj : j ∈ S) (c : ι) :
    (A : Matrix ι ι R) j c = if j = c then 1 else 0 := (h j hj).1 c

theorem ClearedOn.col {S : Finset ι} {A : (Matrix ι ι R)ˣ} (h : ClearedOn S A)
    {j : ι} (hj : j ∈ S) (r : ι) :
    (A : Matrix ι ι R) r j = if r = j then 1 else 0 := (h j hj).2 r

/-- An elementary matrix whose two indices avoid the cleared set does not
disturb it. -/
theorem elementaryUnit_clearedOn (S : Finset ι) {a b : ι} (hab : a ≠ b)
    (ha : a ∉ S) (hb : b ∉ S) (c : R) :
    ClearedOn S (elementaryUnit a b hab c) := fun j hj ↦
  elementaryUnit_mem_coordinateBlock_of_ne j a b hab
    (fun h ↦ ha (h ▸ hj)) (fun h ↦ hb (h ▸ hj)) c

theorem ClearedOn.mul {S : Finset ι} {A B : (Matrix ι ι R)ˣ}
    (hA : ClearedOn S A) (hB : ClearedOn S B) : ClearedOn S (A * B) :=
  fun j hj ↦ mul_mem (hA j hj) (hB j hj)

theorem clearedOn_one (S : Finset ι) : ClearedOn S (1 : (Matrix ι ι R)ˣ) :=
  fun _ _ ↦ one_mem _

/-! ### Producing a nonzero pivot -/

/-- One column move puts a nonzero entry at `(k, k)` without disturbing the
cleared set. -/
theorem exists_pivot [Nontrivial R] (A : (Matrix ι ι R)ˣ) (S : Finset ι)
    (hA : ClearedOn S A) (k : ι) (hk : k ∉ S) :
    ∃ M : (Matrix ι ι R)ˣ, Reaches A M ∧ ClearedOn S M ∧
      (M : Matrix ι ι R) k k ≠ 0 := by
  by_cases hkk : (A : Matrix ι ι R) k k = 0
  · obtain ⟨j, hj⟩ := exists_ne_zero_in_row A k
    have hjk : j ≠ k := by
      rintro rfl
      exact hj hkk
    have hjS : j ∉ S := by
      intro hjS
      apply hj
      rw [hA.col hjS k, if_neg (Ne.symm hjk)]
    refine ⟨A * elementaryUnit j k hjk 1,
      Reaches.right (elementaryUnit_mem j k hjk 1),
      hA.mul (elementaryUnit_clearedOn S hjk hjS hk 1), ?_⟩
    rw [Units.val_mul, mul_elementaryUnit_apply, if_pos rfl, hkk, zero_add,
      mul_one]
    exact hj
  · exact ⟨A, Reaches.refl A, hA, hkk⟩

/-! ### Planting a `1` on the diagonal at the target index -/

/-- Two elementary moves put a literal `1` at `(t, t)`, given a nonzero pivot
at `(k, k)`.  Both moves are supported on the indices `k` and `t`, so the
cleared set survives.

This is the first half of `PropertyTT`'s `exists_four_move_pivot`; the other
half zeroes the `(k, t)` and `(t, k)` entries, which the iteration below does
not need because the simultaneous clearing does it anyway. -/
theorem exists_diag_one [Nontrivial R] (hdiv : HasSingleSandwichDivision R)
    (A : (Matrix ι ι R)ˣ) (S : Finset ι) (hA : ClearedOn S A)
    (k t : ι) (hk : k ∉ S) (ht : t ∉ S) (hkt : k ≠ t)
    (hkk : (A : Matrix ι ι R) k k ≠ 0) :
    ∃ M : (Matrix ι ι R)ˣ, Reaches A M ∧ ClearedOn S M ∧
      (M : Matrix ι ι R) t t = 1 := by
  obtain ⟨p, q, hpq⟩ := hdiv ((A : Matrix ι ι R) k k) hkk
  -- move 1: make the `(k, t)` entry left invertible
  obtain ⟨rho, hrho⟩ : ∃ rho : R,
      p * ((A : Matrix ι ι R) k t + (A : Matrix ι ι R) k k * rho) = 1 :=
    ⟨q * (1 - p * (A : Matrix ι ι R) k t), by
      calc p * ((A : Matrix ι ι R) k t + (A : Matrix ι ι R) k k *
            (q * (1 - p * (A : Matrix ι ι R) k t)))
          = p * (A : Matrix ι ι R) k t +
              p * (A : Matrix ι ι R) k k * q *
                (1 - p * (A : Matrix ι ι R) k t) := by noncomm_ring
        _ = 1 := by rw [hpq, one_mul]; noncomm_ring⟩
  obtain ⟨A₁, hA₁r, hA₁cl, hA₁kt⟩ :
      ∃ A₁ : (Matrix ι ι R)ˣ, Reaches A A₁ ∧ ClearedOn S A₁ ∧
        (A₁ : Matrix ι ι R) k t =
          (A : Matrix ι ι R) k t + (A : Matrix ι ι R) k k * rho := by
    refine ⟨A * elementaryUnit k t hkt rho,
      Reaches.right (elementaryUnit_mem k t hkt rho),
      hA.mul (elementaryUnit_clearedOn S hkt hk ht rho), ?_⟩
    rw [Units.val_mul, mul_elementaryUnit_apply, if_pos rfl]
  have hpb : p * (A₁ : Matrix ι ι R) k t = 1 := by rw [hA₁kt]; exact hrho
  -- move 2: plant a literal `1` at `(t, t)`
  obtain ⟨w, hw⟩ : ∃ w : R,
      (A₁ : Matrix ι ι R) t t + w * (A₁ : Matrix ι ι R) k t = 1 :=
    ⟨(1 - (A₁ : Matrix ι ι R) t t) * p, by
      rw [mul_assoc, hpb, mul_one]; noncomm_ring⟩
  refine ⟨elementaryUnit t k (Ne.symm hkt) w * A₁,
    hA₁r.trans (Reaches.left (elementaryUnit_mem t k (Ne.symm hkt) w)),
    (elementaryUnit_clearedOn S (Ne.symm hkt) ht hk w).mul hA₁cl, ?_⟩
  rw [Units.val_mul, elementaryUnit_mul_apply, if_pos rfl]
  exact hw

/-! ### The clearing step -/

/-- Elementary factors clearing the rest of row `t` lie in `EL_ι(R)`. -/
theorem rightClearFactors_prod_mem (t : ι) (f : ι → R) :
    ((rightClearFactors t f (otherIndices t)).prod : (Matrix ι ι R)ˣ) ∈
      elementaryGroup ι R := by
  refine Subgroup.list_prod_mem _ fun x hx ↦ ?_
  obtain ⟨a, b, hab, c, rfl⟩ := rightClearFactors_elementary t f _ x hx
  exact elementaryUnit_mem a b hab c

/-- Elementary factors clearing the rest of column `t` lie in `EL_ι(R)`. -/
theorem leftClearFactors_prod_mem (t : ι) (f : ι → R) :
    ((leftClearFactors t f (otherIndices t)).prod : (Matrix ι ι R)ˣ) ∈
      elementaryGroup ι R := by
  refine Subgroup.list_prod_mem _ fun x hx ↦ ?_
  obtain ⟨a, b, hab, c, rfl⟩ := leftClearFactors_elementary t f _ x hx
  exact elementaryUnit_mem a b hab c

/-- Clearing row `t` does not disturb the cleared set: the factor at an index
of `S` carries the coefficient `0`, and every other factor avoids `S`. -/
theorem rightClearFactors_clearedOn (S : Finset ι) {t : ι} (ht : t ∉ S)
    (f : ι → R) (hf : ∀ j ∈ S, f j = 0) :
    ClearedOn S ((rightClearFactors t f (otherIndices t)).prod) := by
  intro j hj
  refine Subgroup.list_prod_mem _ fun x hx ↦ ?_
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  by_cases haj : (a : ι) = j
  · rw [show f (a : ι) = 0 from by rw [haj]; exact hf j hj, elementaryUnit_zero]
    exact one_mem _
  · exact elementaryUnit_mem_coordinateBlock_of_ne j t (a : ι)
      a.property.symm (fun h ↦ ht (h ▸ hj)) (fun h ↦ haj h.symm) (f a)

/-- Clearing column `t` does not disturb the cleared set. -/
theorem leftClearFactors_clearedOn (S : Finset ι) {t : ι} (ht : t ∉ S)
    (f : ι → R) (hf : ∀ j ∈ S, f j = 0) :
    ClearedOn S ((leftClearFactors t f (otherIndices t)).prod) := by
  intro j hj
  refine Subgroup.list_prod_mem _ fun x hx ↦ ?_
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  by_cases haj : (a : ι) = j
  · rw [show f (a : ι) = 0 from by rw [haj]; exact hf j hj, elementaryUnit_zero]
    exact one_mem _
  · exact elementaryUnit_mem_coordinateBlock_of_ne j (a : ι) t
      a.property (fun h ↦ haj h.symm) (fun h ↦ ht (h ▸ hj)) (f a)

/-- **One more index clears.**  With a pivot index `k` and a target index `t`
outside the already cleared set, elementary moves produce a matrix cleared on
`insert t S`. -/
theorem exists_clear_step [Nontrivial R] (hdiv : HasSingleSandwichDivision R)
    (A : (Matrix ι ι R)ˣ) (S : Finset ι) (hA : ClearedOn S A)
    (k t : ι) (hk : k ∉ S) (ht : t ∉ S) (hkt : k ≠ t) :
    ∃ M : (Matrix ι ι R)ˣ, Reaches A M ∧ ClearedOn (insert t S) M := by
  obtain ⟨A₀, hA₀r, hA₀, hA₀k⟩ := exists_pivot A S hA k hk
  obtain ⟨C, hCr, hCcl, hCtt⟩ :=
    exists_diag_one hdiv A₀ S hA₀ k t hk ht hkt hA₀k
  -- clear the rest of row `t`
  have hCcoef : ∀ j ∈ S, -(C : Matrix ι ι R) t j = 0 := by
    intro j hj
    rw [hCcl.col hj t, if_neg (fun h : t = j ↦ ht (h ▸ hj)), neg_zero]
  obtain ⟨D, hDr, hDcl, hDrow⟩ :
      ∃ D : (Matrix ι ι R)ˣ, Reaches C D ∧ ClearedOn S D ∧
        ∀ c : ι, (D : Matrix ι ι R) t c = if t = c then 1 else 0 := by
    refine ⟨C * (rightClearFactors t (fun c ↦ -(C : Matrix ι ι R) t c)
        (otherIndices t)).prod,
      Reaches.right (rightClearFactors_prod_mem t _),
      hCcl.mul (rightClearFactors_clearedOn S ht _ hCcoef), fun c ↦ ?_⟩
    rw [Units.val_mul]
    exact rightClearFactors_clear_row (C : Matrix ι ι R) t hCtt c
  -- clear the rest of column `t`
  have hDcoef : ∀ j ∈ S, -(D : Matrix ι ι R) j t = 0 := by
    intro j hj
    rw [hDcl.row hj t, if_neg (fun h : j = t ↦ ht (h ▸ hj)), neg_zero]
  refine ⟨(leftClearFactors t (fun r ↦ -(D : Matrix ι ι R) r t)
      (otherIndices t)).prod * D,
    hA₀r.trans (hCr.trans (hDr.trans
      (Reaches.left (leftClearFactors_prod_mem t _)))), ?_⟩
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hjS
  · exact leftClearFactors_make_coordinateBlock D j hDrow
  · exact mul_mem
      ((leftClearFactors_clearedOn S ht _ hDcoef) j hjS) (hDcl j hjS)

/-! ### The diagonal endpoint -/

/-- The diagonal unit carrying `u` at `l` and `1` elsewhere. -/
def diagAt (l : ι) (u : Rˣ) : (Matrix ι ι R)ˣ where
  val := Matrix.diagonal fun i ↦ if i = l then (u : R) else 1
  inv := Matrix.diagonal fun i ↦ if i = l then ((u⁻¹ : Rˣ) : R) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : i = l <;> simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : i = l <;> simp [h]

@[simp] theorem diagAt_val (l : ι) (u : Rˣ) :
    ((diagAt l u : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      Matrix.diagonal fun i ↦ if i = l then (u : R) else 1 := rfl

/-- A matrix cleared everywhere except at `l` is `diagAt l u`. -/
theorem exists_eq_diagAt {M : (Matrix ι ι R)ˣ} {l : ι}
    (h : ClearedOn (Finset.univ.erase l) M) : ∃ u : Rˣ, M = diagAt l u := by
  classical
  have hmem : ∀ x : ι, x ≠ l → x ∈ Finset.univ.erase l := fun x hx ↦
    Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩
  have hoff : ∀ x y : ι, x ≠ y → (M : Matrix ι ι R) x y = 0 := by
    intro x y hxy
    by_cases hx : x = l
    · have hy : y ≠ l := fun hyl ↦ hxy (hx.trans hyl.symm)
      rw [h.col (hmem y hy) x, if_neg hxy]
    · rw [h.row (hmem x hx) y, if_neg hxy]
  have hdiag : ∀ x : ι, x ≠ l → (M : Matrix ι ι R) x x = 1 := fun x hx ↦ by
    rw [h.row (hmem x hx) x, if_pos rfl]
  have hmul : (M : Matrix ι ι R) l l *
      ((M⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) l l = 1 := by
    have hv := congrFun (congrFun M.mul_inv l) l
    rw [Matrix.mul_apply, Matrix.one_apply_eq,
      Finset.sum_eq_single l
        (fun y _ hy ↦ by rw [hoff l y (Ne.symm hy), zero_mul])
        (fun hcon ↦ absurd (Finset.mem_univ l) hcon)] at hv
    exact hv
  have hmul' : ((M⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) l l *
      (M : Matrix ι ι R) l l = 1 := by
    have hv := congrFun (congrFun M.inv_mul l) l
    rw [Matrix.mul_apply, Matrix.one_apply_eq,
      Finset.sum_eq_single l
        (fun y _ hy ↦ by rw [hoff y l hy, mul_zero])
        (fun hcon ↦ absurd (Finset.mem_univ l) hcon)] at hv
    exact hv
  refine ⟨⟨(M : Matrix ι ι R) l l,
    ((M⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) l l, hmul, hmul'⟩, ?_⟩
  apply Units.ext
  rw [diagAt_val]
  ext x y
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.diagonal_apply_eq]
    by_cases hx : x = l
    · rw [if_pos hx, hx]
    · rw [if_neg hx]
      exact hdiag x hx
  · rw [Matrix.diagonal_apply_ne _ hxy]
    exact hoff x y hxy

/-! ### Elimination at every rank -/

/-- Clearing every index other than `l`, one index at a time, always pivoting
on `l`. -/
theorem exists_cleared_erase [Nontrivial R] (hdiv : HasSingleSandwichDivision R)
    (l : ι) :
    ∀ (n : ℕ) (S : Finset ι) (A : (Matrix ι ι R)ˣ), l ∉ S →
      (Finset.univ.erase l \ S).card = n → ClearedOn S A →
      ∃ M : (Matrix ι ι R)ˣ, Reaches A M ∧
        ClearedOn (Finset.univ.erase l) M := by
  classical
  intro n
  induction n with
  | zero =>
      intro S A _ hcard hA
      exact ⟨A, Reaches.refl A, hA.mono
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard))⟩
  | succ n IH =>
      intro S A hlS hcard hA
      have hne : (Finset.univ.erase l \ S).Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨m, hm⟩ := hne
      have hmS : m ∉ S := (Finset.mem_sdiff.mp hm).2
      have hml : m ≠ l := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hm).1).1
      obtain ⟨M, hMr, hM⟩ :=
        exists_clear_step hdiv A S hA l m hlS hmS (Ne.symm hml)
      have hset : Finset.univ.erase l \ insert m S =
          (Finset.univ.erase l \ S).erase m := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_univ, and_true, not_or]
        tauto
      have hcard' : (Finset.univ.erase l \ insert m S).card = n := by
        rw [hset, Finset.card_erase_of_mem hm, hcard]
        omega
      have hlS' : l ∉ insert m S := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h ↦ hml h.symm, hlS⟩
      obtain ⟨N, hNr, hN⟩ := IH (insert m S) M hlS' hcard' hM
      exact ⟨N, hMr.trans hNr, hN⟩

/-- **Gaussian elimination at every rank.**  Over a nontrivial ring in which
every nonzero element divides the identity on both sides, elementary row and
column operations carry every invertible matrix to a diagonal matrix that is
the identity away from a prescribed index.

At `ι = Fin 2` this is `MatrixDiagonalization.exists_elementary_mul_diag`; the
content here is that the rank and the surviving index are arbitrary. -/
theorem exists_elementary_mul_diagAt [Nontrivial R]
    (hdiv : HasSingleSandwichDivision R) (A : (Matrix ι ι R)ˣ) (l : ι) :
    ∃ E ∈ elementaryGroup ι R, ∃ F ∈ elementaryGroup ι R, ∃ u : Rˣ,
      E * A * F = diagAt l u := by
  classical
  obtain ⟨M, hMr, hM⟩ := exists_cleared_erase hdiv l
    (Finset.univ.erase l \ (∅ : Finset ι)).card ∅ A
    (Finset.notMem_empty l) rfl (clearedOn_empty _)
  obtain ⟨u, hu⟩ := exists_eq_diagAt hM
  obtain ⟨E, hE, F, hF, hEF⟩ := hMr
  exact ⟨E, hE, F, hF, u, by rw [← hEF]; exact hu⟩

/-- The elimination read as a factorization: every invertible matrix lies in
`EL_ι(R) · diagAt l u · EL_ι(R)`. -/
theorem eq_elementary_mul_diagAt [Nontrivial R]
    (hdiv : HasSingleSandwichDivision R) (A : (Matrix ι ι R)ˣ) (l : ι) :
    ∃ E ∈ elementaryGroup ι R, ∃ F ∈ elementaryGroup ι R, ∃ u : Rˣ,
      A = E * diagAt l u * F := by
  obtain ⟨E, hE, F, hF, u, hEF⟩ := exists_elementary_mul_diagAt hdiv A l
  refine ⟨E⁻¹, inv_mem hE, F⁻¹, inv_mem hF, u, ?_⟩
  rw [← hEF]
  group

end RankNElimination
end GroupApproximation
