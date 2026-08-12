import GroupApproximation.PropertyTT.RingHypotheses

/-!
# Rank-independent strong-division pivot

This is the local matrix calculation behind bounded generation.  It is
proved for an arbitrary finite index type and arbitrary two distinct
coordinates.  Four elementary operations turn a nonzero pivot into an
isolated `2 × 2` cross with a literal `1` in the second diagonal position.
-/

namespace GroupApproximation

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

/-- A single elementary transvection, viewed in the ambient general linear
group.  This predicate remembers word length; subgroup membership alone does
not. -/
def IsElementaryUnit (x : (Matrix ι ι R)ˣ) : Prop :=
  ∃ i j : ι, ∃ hij : i ≠ j, ∃ a : R, x = elementaryUnit i j hij a

/-- Right multiplication by `xᵢⱼ(a)` changes only column `j`. -/
theorem mul_elementaryUnit_apply (M : Matrix ι ι R)
    (i j : ι) (hij : i ≠ j) (a : R) (r c : ι) :
    (M * (elementaryUnit i j hij a : (Matrix ι ι R)ˣ)) r c =
      if c = j then M r j + M r i * a else M r c := by
  rw [show ((elementaryUnit i j hij a : (Matrix ι ι R)ˣ) :
      Matrix ι ι R) = 1 + Matrix.single i j a from rfl]
  rw [mul_add, mul_one, Matrix.add_apply]
  by_cases hc : c = j
  · subst c
    rw [if_pos rfl]
    exact congrArg (M r j + ·) (Matrix.mul_single_apply_same a i j r M)
  · rw [if_neg hc]
    have hz := Matrix.mul_single_apply_of_ne a i j r c hc M
    rw [hz, add_zero]

/-- Left multiplication by `xᵢⱼ(a)` changes only row `i`. -/
theorem elementaryUnit_mul_apply (M : Matrix ι ι R)
    (i j : ι) (hij : i ≠ j) (a : R) (r c : ι) :
    ((elementaryUnit i j hij a : (Matrix ι ι R)ˣ) * M) r c =
      if r = i then M i c + a * M j c else M r c := by
  rw [show ((elementaryUnit i j hij a : (Matrix ι ι R)ˣ) :
      Matrix ι ι R) = 1 + Matrix.single i j a from rfl]
  rw [add_mul, one_mul, Matrix.add_apply]
  by_cases hr : r = i
  · subst r
    rw [if_pos rfl]
    exact congrArg (M i c + ·) (Matrix.single_mul_apply_same a i j c M)
  · rw [if_neg hr]
    have hz := Matrix.single_mul_apply_of_ne a i j r c hr M
    rw [hz, add_zero]

/-- Four elementary moves plant a literal `1` at `(j,j)` and clear the two
off-diagonal entries in the `(i,j)` coordinate plane.  The ambient matrix
may have arbitrary size; invertibility of the displayed `2 × 2` corner is
not assumed. -/
theorem exists_four_move_pivot
    (hdiv : HasSingleSandwichDivision R)
    (A : (Matrix ι ι R)ˣ) (i j : ι) (hij : i ≠ j)
    (hpivot : (A : Matrix ι ι R) i i ≠ 0) :
    ∃ E F : (Matrix ι ι R)ˣ,
      E ∈ elementaryGroup ι R ∧ F ∈ elementaryGroup ι R ∧
      ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j j = 1 ∧
      ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j = 0 ∧
      ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j i = 0 ∧
      ∃ l r : List (Matrix ι ι R)ˣ,
        l.length ≤ 2 ∧ r.length ≤ 2 ∧
        (∀ x ∈ l, IsElementaryUnit x) ∧
        (∀ x ∈ r, IsElementaryUnit x) ∧
        l.prod = E ∧ r.prod = F := by
  let a := (A : Matrix ι ι R) i i
  let b := (A : Matrix ι ι R) i j
  obtain ⟨p, q, hpq⟩ := hdiv a hpivot
  let rho : R := q * (1 - p * b)
  let F₁ : (Matrix ι ι R)ˣ := elementaryUnit i j hij rho
  let A₁ : (Matrix ι ι R)ˣ := A * F₁
  let b₁ : R := (A₁ : Matrix ι ι R) i j
  have hb₁ : b₁ = a * rho + b := by
    simp only [b₁, A₁, Units.val_mul, F₁]
    rw [mul_elementaryUnit_apply]
    simp [a, b, add_comm]
  have hpb₁ : p * b₁ = 1 := by
    rw [hb₁]
    dsimp [rho]
    calc
      p * (a * (q * (1 - p * b)) + b) =
          p * a * q * (1 - p * b) + p * b := by
        rw [mul_add]
        congr 1
        rw [← mul_assoc, ← mul_assoc]
      _ = 1 := by
        rw [hpq, one_mul]
        noncomm_ring
  let d₁ : R := (A₁ : Matrix ι ι R) j j
  let w : R := (1 - d₁) * p
  let E₁ : (Matrix ι ι R)ˣ := elementaryUnit j i hij.symm w
  let A₂ : (Matrix ι ι R)ˣ := E₁ * A₁
  have hA₂jj : (A₂ : Matrix ι ι R) j j = 1 := by
    simp only [A₂, Units.val_mul, E₁]
    rw [elementaryUnit_mul_apply]
    rw [if_pos rfl]
    change d₁ + w * b₁ = 1
    rw [show w * b₁ = 1 - d₁ from by
      dsimp [w]
      rw [mul_assoc, hpb₁, mul_one]]
    abel
  have hA₂ij : (A₂ : Matrix ι ι R) i j = b₁ := by
    simp only [A₂, Units.val_mul, E₁]
    rw [elementaryUnit_mul_apply]
    rw [if_neg hij]
  let E₂ : (Matrix ι ι R)ˣ := elementaryUnit i j hij (-b₁)
  let A₃ : (Matrix ι ι R)ˣ := E₂ * A₂
  have hA₃ij : (A₃ : Matrix ι ι R) i j = 0 := by
    simp only [A₃, Units.val_mul, E₂]
    rw [elementaryUnit_mul_apply]
    rw [if_pos rfl, hA₂ij, hA₂jj]
    simp
  have hA₃jj : (A₃ : Matrix ι ι R) j j = 1 := by
    simp only [A₃, Units.val_mul, E₂]
    rw [elementaryUnit_mul_apply]
    rw [if_neg hij.symm, hA₂jj]
  let c₃ : R := (A₃ : Matrix ι ι R) j i
  let F₂ : (Matrix ι ι R)ˣ := elementaryUnit j i hij.symm (-c₃)
  let A₄ : (Matrix ι ι R)ˣ := A₃ * F₂
  have hA₄ji : (A₄ : Matrix ι ι R) j i = 0 := by
    simp only [A₄, Units.val_mul, F₂]
    rw [mul_elementaryUnit_apply]
    rw [if_pos rfl, hA₃jj]
    change c₃ + 1 * -c₃ = 0
    simp
  have hA₄ij : (A₄ : Matrix ι ι R) i j = 0 := by
    simp only [A₄, Units.val_mul, F₂]
    rw [mul_elementaryUnit_apply]
    rw [if_neg hij.symm, hA₃ij]
  have hA₄jj : (A₄ : Matrix ι ι R) j j = 1 := by
    simp only [A₄, Units.val_mul, F₂]
    rw [mul_elementaryUnit_apply]
    rw [if_neg hij.symm, hA₃jj]
  have hfactor : (E₂ * E₁) * A * (F₁ * F₂) = A₄ := by
    dsimp [A₄, A₃, A₂, A₁]
    group
  refine ⟨E₂ * E₁, F₁ * F₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _)
      (elementaryUnit_mem _ _ _ _)
  · exact Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _)
      (elementaryUnit_mem _ _ _ _)
  · rw [hfactor]
    exact hA₄jj
  · rw [hfactor]
    exact hA₄ij
  · rw [hfactor]
    exact hA₄ji
  · refine ⟨[E₂, E₁], [F₁, F₂], by simp, by simp, ?_, ?_, by simp, by simp⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨i, j, hij, -b₁, rfl⟩
      · exact ⟨j, i, hij.symm, w, rfl⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨i, j, hij, rho, rfl⟩
      · exact ⟨j, i, hij.symm, -c₃, rfl⟩

/-- A row of an invertible matrix over a nontrivial ring is nonzero. -/
theorem exists_ne_zero_in_row [Nontrivial R]
    (A : (Matrix ι ι R)ˣ) (i : ι) :
    ∃ k : ι, (A : Matrix ι ι R) i k ≠ 0 := by
  by_contra h
  push Not at h
  have hinv := A.val_inv
  have hii := congrFun (congrFun hinv i) i
  rw [Matrix.mul_apply] at hii
  have hzero : ∑ k, (A : Matrix ι ι R) i k *
      A.inv k i = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [h k, zero_mul]
  rw [hzero] at hii
  have hone : (1 : Matrix ι ι R) i i = (1 : R) := by simp
  rw [hone] at hii
  exact zero_ne_one hii

/-- Two elementary moves plant a literal `1` at `(j,j)` once the chosen
`(i,i)` pivot is nonzero.  The off-diagonal entries are deliberately left
for the subsequent full row and column sweeps. -/
theorem exists_two_move_diagonal_pivot
    (hdiv : HasSingleSandwichDivision R)
    (A : (Matrix ι ι R)ˣ) (i j : ι) (hij : i ≠ j)
    (hpivot : (A : Matrix ι ι R) i i ≠ 0) :
    ∃ E F : (Matrix ι ι R)ˣ,
      IsElementaryUnit E ∧ IsElementaryUnit F ∧
      ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j j = 1 := by
  let a := (A : Matrix ι ι R) i i
  let b := (A : Matrix ι ι R) i j
  obtain ⟨p, q, hpq⟩ := hdiv a hpivot
  let rho : R := q * (1 - p * b)
  let F : (Matrix ι ι R)ˣ := elementaryUnit i j hij rho
  let A₁ : (Matrix ι ι R)ˣ := A * F
  let b₁ : R := (A₁ : Matrix ι ι R) i j
  have hb₁ : b₁ = a * rho + b := by
    simp only [b₁, A₁, Units.val_mul, F]
    rw [mul_elementaryUnit_apply]
    simp [a, b, add_comm]
  have hpb₁ : p * b₁ = 1 := by
    rw [hb₁]
    dsimp [rho]
    calc
      p * (a * (q * (1 - p * b)) + b) =
          p * a * q * (1 - p * b) + p * b := by
        rw [mul_add]
        congr 1
        rw [← mul_assoc, ← mul_assoc]
      _ = 1 := by
        rw [hpq, one_mul]
        noncomm_ring
  let d₁ : R := (A₁ : Matrix ι ι R) j j
  let w : R := (1 - d₁) * p
  let E : (Matrix ι ι R)ˣ := elementaryUnit j i hij.symm w
  have hjj : ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j j = 1 := by
    rw [show E * A * F = E * A₁ from by dsimp [A₁]; group]
    simp only [Units.val_mul, E]
    rw [elementaryUnit_mul_apply]
    rw [if_pos rfl]
    change d₁ + w * b₁ = 1
    rw [show w * b₁ = 1 - d₁ from by
      dsimp [w]
      rw [mul_assoc, hpb₁, mul_one]]
    abel
  exact ⟨E, F, ⟨j, i, hij.symm, w, rfl⟩,
    ⟨i, j, hij, rho, rfl⟩, hjj⟩

/-- At most one preliminary column addition followed by the two-move pivot
plants a literal `1` at `(j,j)`.  The factor lists retain the separate bounds
needed by the coordinate-block factorization. -/
theorem exists_three_move_diagonal_pivot [Nontrivial R]
    (hdiv : HasSingleSandwichDivision R)
    (A : (Matrix ι ι R)ˣ) (i j : ι) (hij : i ≠ j) :
    ∃ E F : (Matrix ι ι R)ˣ,
      ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j j = 1 ∧
      ∃ l r : List (Matrix ι ι R)ˣ,
        l.length ≤ 1 ∧ r.length ≤ 2 ∧
        (∀ x ∈ l, IsElementaryUnit x) ∧
        (∀ x ∈ r, IsElementaryUnit x) ∧
        l.prod = E ∧ r.prod = F := by
  by_cases hii : (A : Matrix ι ι R) i i ≠ 0
  · obtain ⟨E, F, hE, hF, hjj⟩ :=
      exists_two_move_diagonal_pivot hdiv A i j hij hii
    exact ⟨E, F, hjj, [E], [F], by simp, by simp,
      by simpa using hE, by simpa using hF, by simp, by simp⟩
  push Not at hii
  obtain ⟨k, hk⟩ := exists_ne_zero_in_row A i
  have hki : k ≠ i := by
    intro h
    subst k
    exact hk hii
  let F₀ : (Matrix ι ι R)ˣ := elementaryUnit k i hki 1
  let A₀ : (Matrix ι ι R)ˣ := A * F₀
  have hcorner : (A₀ : Matrix ι ι R) i i ≠ 0 := by
    simp only [A₀, Units.val_mul, F₀]
    rw [mul_elementaryUnit_apply]
    rw [if_pos rfl, hii, zero_add, mul_one]
    exact hk
  obtain ⟨E, F, hE, hF, hjj⟩ :=
    exists_two_move_diagonal_pivot hdiv A₀ i j hij hcorner
  refine ⟨E, F₀ * F, ?_, [E], [F₀, F], by simp, by simp,
    by simpa using hE, ?_, by simp, by simp⟩
  · rw [← hjj]
    dsimp [A₀]
    group
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨k, i, hki, 1, rfl⟩
    · exact hF

/-- At most one preliminary column addition makes the chosen corner nonzero;
the four-move pivot then applies. -/
theorem exists_five_move_pivot [Nontrivial R]
    (hdiv : HasSingleSandwichDivision R)
    (A : (Matrix ι ι R)ˣ) (i j : ι) (hij : i ≠ j) :
    ∃ E F : (Matrix ι ι R)ˣ,
      E ∈ elementaryGroup ι R ∧ F ∈ elementaryGroup ι R ∧
      ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j j = 1 ∧
      ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j = 0 ∧
      ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j i = 0 ∧
      ∃ l r : List (Matrix ι ι R)ˣ,
        l.length ≤ 2 ∧ r.length ≤ 3 ∧
        (∀ x ∈ l, IsElementaryUnit x) ∧
        (∀ x ∈ r, IsElementaryUnit x) ∧
        l.prod = E ∧ r.prod = F := by
  by_cases hii : (A : Matrix ι ι R) i i ≠ 0
  · obtain ⟨E, F, hE, hF, hjj, hij0, hji0,
        l, r, hl, hr, hlel, hrel, hlE, hrF⟩ :=
      exists_four_move_pivot hdiv A i j hij hii
    exact ⟨E, F, hE, hF, hjj, hij0, hji0,
      l, r, hl, hr.trans (by omega), hlel, hrel, hlE, hrF⟩
  push Not at hii
  obtain ⟨k, hk⟩ := exists_ne_zero_in_row A i
  have hki : k ≠ i := by
    intro h
    subst k
    exact hk hii
  let F₀ : (Matrix ι ι R)ˣ := elementaryUnit k i hki 1
  let A₀ : (Matrix ι ι R)ˣ := A * F₀
  have hcorner : (A₀ : Matrix ι ι R) i i ≠ 0 := by
    simp only [A₀, Units.val_mul, F₀]
    rw [mul_elementaryUnit_apply]
    rw [if_pos rfl, hii, zero_add, mul_one]
    exact hk
  obtain ⟨E, F, hE, hF, hjj, hij0, hji0,
      l, r, hl, hr, hlel, hrel, hlE, hrF⟩ :=
    exists_four_move_pivot hdiv A₀ i j hij hcorner
  refine ⟨E, F₀ * F, hE,
    Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _) hF, ?_, ?_, ?_, ?_⟩
  · rw [← hjj]
    dsimp [A₀]
    group
  · rw [← hij0]
    dsimp [A₀]
    group
  · rw [← hji0]
    dsimp [A₀]
    group
  · refine ⟨l, F₀ :: r, hl, ?_, hlel, ?_, hlE, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨k, i, hki, 1, rfl⟩
      · exact hrel x hx
    · simp [hrF]

/-! ### Simultaneous row clearing -/

/-- A list of right transvections with common source column `j`. -/
def rightClearFactors (j : ι) (f : ι → R)
    (l : List {k : ι // k ≠ j}) : List (Matrix ι ι R)ˣ :=
  l.map fun k : {k : ι // k ≠ j} ↦
    elementaryUnit j (k : ι) k.property.symm (f k)

/-- The product of distinct common-source right transvections changes each
listed column independently. -/
theorem mul_rightClearFactors_apply (A : Matrix ι ι R) (j : ι)
    (f : ι → R) (l : List {k : ι // k ≠ j}) (hl : l.Nodup)
    (r c : ι) :
    (A * ((rightClearFactors j f l).prod : (Matrix ι ι R)ˣ)) r c =
      if c ∈ l.map ((↑·) : {k : ι // k ≠ j} → ι)
      then A r c + A r j * f c else A r c := by
  induction l generalizing A with
  | nil => simp [rightClearFactors]
  | cons k l ih =>
      have hknmem : k ∉ l := (List.nodup_cons.mp hl).1
      have hltail : l.Nodup := (List.nodup_cons.mp hl).2
      let T : (Matrix ι ι R)ˣ := elementaryUnit j k k.property.symm (f k)
      let B : Matrix ι ι R := A * (T : Matrix ι ι R)
      have hprod : ((rightClearFactors j f (k :: l)).prod :
          (Matrix ι ι R)) =
          (T : Matrix ι ι R) *
            ((rightClearFactors j f l).prod : (Matrix ι ι R)ˣ) := by
        simp [rightClearFactors, T]
      rw [hprod, ← Matrix.mul_assoc]
      change (B * ((rightClearFactors j f l).prod :
        (Matrix ι ι R)ˣ)) r c = _
      rw [ih B hltail]
      have hBj : B r j = A r j := by
        dsimp [B, T]
        rw [mul_elementaryUnit_apply]
        rw [if_neg k.property.symm]
      by_cases hctail : c ∈ l.map ((↑·) : {k : ι // k ≠ j} → ι)
      · have hck : c ≠ k := by
          intro hck
          subst c
          obtain ⟨x, hx, hxval⟩ := List.mem_map.mp hctail
          have hxk : x = k := Subtype.ext hxval
          exact hknmem (hxk ▸ hx)
        have hBc : B r c = A r c := by
          dsimp [B, T]
          rw [mul_elementaryUnit_apply]
          rw [if_neg hck]
        rw [if_pos hctail, hBc, hBj]
        rw [if_pos (show c ∈
          (k :: l).map ((↑·) : {k : ι // k ≠ j} → ι) by
            rw [List.map_cons, List.mem_cons]
            exact Or.inr hctail)]
      · by_cases hck : c = k
        · subst c
          have hkhead : (k : ι) ∈
              (k :: l).map ((↑·) : {k : ι // k ≠ j} → ι) := by simp
          rw [if_neg hctail]
          have hBk : B r (k : ι) = A r k + A r j * f k := by
            dsimp [B, T]
            rw [mul_elementaryUnit_apply]
            rw [if_pos rfl]
          rw [hBk, if_pos hkhead]
        · have hcnmem : c ∉
              (k :: l).map ((↑·) : {k : ι // k ≠ j} → ι) := by
            rw [List.map_cons, List.mem_cons]
            exact fun h ↦ h.elim hck hctail
          rw [if_neg hctail]
          have hBc : B r c = A r c := by
            dsimp [B, T]
            rw [mul_elementaryUnit_apply]
            rw [if_neg hck]
          rw [hBc, if_neg hcnmem]

/-! ### Simultaneous column clearing -/

/-- A list of left transvections with common source row `j`. -/
def leftClearFactors (j : ι) (f : ι → R)
    (l : List {k : ι // k ≠ j}) : List (Matrix ι ι R)ˣ :=
  l.map fun k : {k : ι // k ≠ j} ↦
    elementaryUnit (k : ι) j k.property (f k)

/-- The product of distinct common-source left transvections changes each
listed row independently. -/
theorem leftClearFactors_mul_apply (A : Matrix ι ι R) (j : ι)
    (f : ι → R) (l : List {k : ι // k ≠ j}) (hl : l.Nodup)
    (r c : ι) :
    (((leftClearFactors j f l).prod : (Matrix ι ι R)ˣ) * A) r c =
      if r ∈ l.map ((↑·) : {k : ι // k ≠ j} → ι)
      then A r c + f r * A j c else A r c := by
  induction l generalizing A r c with
  | nil => simp [leftClearFactors]
  | cons k l ih =>
      have hknmem : k ∉ l := (List.nodup_cons.mp hl).1
      have hltail : l.Nodup := (List.nodup_cons.mp hl).2
      let T : (Matrix ι ι R)ˣ := elementaryUnit (k : ι) j k.property (f k)
      let B : Matrix ι ι R :=
        ((leftClearFactors j f l).prod : (Matrix ι ι R)ˣ) * A
      have hprod : ((leftClearFactors j f (k :: l)).prod :
          Matrix ι ι R) =
          (T : Matrix ι ι R) *
            ((leftClearFactors j f l).prod : (Matrix ι ι R)ˣ) := by
        simp [leftClearFactors, T]
      rw [hprod, Matrix.mul_assoc]
      change ((T : Matrix ι ι R) * B) r c = _
      have hBj : B j c = A j c := by
        dsimp [B]
        rw [ih (A := A) (r := j) (c := c) hltail]
        rw [if_neg (show j ∉
          l.map ((↑·) : {k : ι // k ≠ j} → ι) by
            intro hj
            obtain ⟨x, _, hx⟩ := List.mem_map.mp hj
            exact x.property hx)]
      rw [elementaryUnit_mul_apply]
      by_cases hrtail : r ∈
          l.map ((↑·) : {k : ι // k ≠ j} → ι)
      · have hrk : r ≠ k := by
          intro hrk
          subst r
          obtain ⟨x, hx, hxval⟩ := List.mem_map.mp hrtail
          have hxk : x = k := Subtype.ext hxval
          exact hknmem (hxk ▸ hx)
        rw [if_neg hrk]
        have hBr : B r c = A r c + f r * A j c := by
          dsimp [B]
          rw [ih (A := A) (r := r) (c := c) hltail, if_pos hrtail]
        rw [hBr]
        rw [if_pos (show r ∈
          (k :: l).map ((↑·) : {k : ι // k ≠ j} → ι) by
            rw [List.map_cons, List.mem_cons]
            exact Or.inr hrtail)]
      · by_cases hrk : r = k
        · subst r
          rw [if_pos rfl]
          have hBk : B (k : ι) c = A k c := by
            dsimp [B]
            rw [ih (A := A) (r := (k : ι)) (c := c) hltail,
              if_neg hrtail]
          rw [hBk, hBj]
          rw [if_pos (show (k : ι) ∈
            (k :: l).map ((↑·) : {k : ι // k ≠ j} → ι) by
              rw [List.map_cons, List.mem_cons]
              exact Or.inl rfl)]
        · rw [if_neg hrk]
          have hBr : B r c = A r c := by
            dsimp [B]
            rw [ih (A := A) (r := r) (c := c) hltail, if_neg hrtail]
          have hrnmem : r ∉
              (k :: l).map ((↑·) : {k : ι // k ≠ j} → ι) := by
            rw [List.map_cons, List.mem_cons]
            exact fun h ↦ h.elim hrk hrtail
          rw [hBr, if_neg hrnmem]

end GroupApproximation
