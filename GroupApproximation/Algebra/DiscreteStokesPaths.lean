import GroupApproximation.Algebra.DiscreteStokes

/-!
# The discrete integral along paths, and the quadrangle identity

`pathPoints f b L` lists the points visited when the word `L` is read from `b`,
both endpoints included.  Three evaluations of the discrete integral
`DiscreteStokes.wordSum f φ ψ b L` of `φ dψ` read off only the values of `φ` and
`ψ` along the path:

* if `φ` vanishes along the path, the integral vanishes;
* if `ψ` is constant along the path, the integral vanishes;
* if `φ` is constant `a` along the path, the integral is `2 a (ψ(end) - ψ(start))`.

Together they give the **quadrangle identity** (`wordSum_quadrangle`): if a word
is cut into four pieces with `φ = 0` along the first, `ψ = 0` along the second,
`φ = a` along the third and `ψ = c` along the fourth, the integral along the whole
word is `2 a c`.  With `φ`, `ψ` truncated distances to the first two pieces, this
is Besicovitch's quadrangle inequality for algebraic area: opposite sides at
distance at least `a` and `c` force area at least `2 a c` divided by the square of
the longest relator.
-/

namespace GroupApproximation
namespace DiscreteStokes

universe u v

variable {α : Type u} {Q : Type v} [Group Q]

/-- **The points visited** when reading `L` from `b`, both endpoints included. -/
def pathPoints (f : α → Q) : Q → List (α × Bool) → List Q
  | b, [] => [b]
  | b, x :: L => b :: pathPoints f (b * letterVal f x) L

@[simp] theorem pathPoints_nil (f : α → Q) (b : Q) : pathPoints f b [] = [b] := rfl

@[simp] theorem pathPoints_cons (f : α → Q) (b : Q) (x : α × Bool) (L : List (α × Bool)) :
    pathPoints f b (x :: L) = b :: pathPoints f (b * letterVal f x) L := rfl

/-- The starting point is visited. -/
theorem start_mem_pathPoints (f : α → Q) (b : Q) (L : List (α × Bool)) :
    b ∈ pathPoints f b L := by
  cases L <;> simp

/-- The endpoint is visited. -/
theorem end_mem_pathPoints (f : α → Q) (b : Q) (L : List (α × Bool)) :
    b * wordVal f L ∈ pathPoints f b L := by
  induction L generalizing b with
  | nil => simp
  | cons x L ih =>
      rw [pathPoints_cons, wordVal_cons, ← mul_assoc]
      exact List.mem_cons_of_mem _ (ih (b * letterVal f x))

/-- The points of a concatenation are the points of the two pieces. -/
theorem mem_pathPoints_append (f : α → Q) (b : Q) (L M : List (α × Bool)) {q : Q}
    (hq : q ∈ pathPoints f b (L ++ M)) :
    q ∈ pathPoints f b L ∨ q ∈ pathPoints f (b * wordVal f L) M := by
  induction L generalizing b with
  | nil => simp only [List.nil_append, wordVal_nil, mul_one] at hq ⊢; exact Or.inr hq
  | cons x L ih =>
      rw [List.cons_append, pathPoints_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Or.inl (start_mem_pathPoints f _ _)
      · rcases ih (b * letterVal f x) hq with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rw [wordVal_cons, ← mul_assoc]
          exact Or.inr h

/-! ## Three evaluations -/

/-- **If `φ` vanishes along the path, the integral vanishes.** -/
theorem wordSum_eq_zero_of_phi_zero (f : α → Q) (φ ψ : Q → ℤ) (b : Q) (L : List (α × Bool))
    (h : ∀ q ∈ pathPoints f b L, φ q = 0) : wordSum f φ ψ b L = 0 := by
  induction L generalizing b with
  | nil => rfl
  | cons x L ih =>
      have hb : φ b = 0 := h b (start_mem_pathPoints f b _)
      have hnext : φ (b * letterVal f x) = 0 :=
        h _ (List.mem_cons_of_mem _ (start_mem_pathPoints f _ L))
      rw [wordSum_cons, ih (b * letterVal f x) (fun q hq => h q (List.mem_cons_of_mem _ hq))]
      unfold edgeTerm
      rw [hb, hnext]
      ring

/-- **If `ψ` is constant along the path, the integral vanishes.** -/
theorem wordSum_eq_zero_of_psi_const (f : α → Q) (φ ψ : Q → ℤ) (b : Q) (L : List (α × Bool))
    (c : ℤ) (h : ∀ q ∈ pathPoints f b L, ψ q = c) : wordSum f φ ψ b L = 0 := by
  induction L generalizing b with
  | nil => rfl
  | cons x L ih =>
      have hb : ψ b = c := h b (start_mem_pathPoints f b _)
      have hnext : ψ (b * letterVal f x) = c :=
        h _ (List.mem_cons_of_mem _ (start_mem_pathPoints f _ L))
      rw [wordSum_cons, ih (b * letterVal f x) (fun q hq => h q (List.mem_cons_of_mem _ hq))]
      unfold edgeTerm
      rw [hb, hnext]
      ring

/-- **If `φ` is constant `a` along the path, the integral telescopes.** -/
theorem wordSum_eq_of_phi_const (f : α → Q) (φ ψ : Q → ℤ) (b : Q) (L : List (α × Bool))
    (a : ℤ) (h : ∀ q ∈ pathPoints f b L, φ q = a) :
    wordSum f φ ψ b L = 2 * a * (ψ (b * wordVal f L) - ψ b) := by
  induction L generalizing b with
  | nil => simp
  | cons x L ih =>
      have hb : φ b = a := h b (start_mem_pathPoints f b _)
      have hnext : φ (b * letterVal f x) = a :=
        h _ (List.mem_cons_of_mem _ (start_mem_pathPoints f _ L))
      rw [wordSum_cons, ih (b * letterVal f x) (fun q hq => h q (List.mem_cons_of_mem _ hq)),
        wordVal_cons, ← mul_assoc]
      unfold edgeTerm
      rw [hb, hnext]
      ring

/-! ## The quadrangle identity -/

/-- **The quadrangle identity.**  Along `w₁ ++ w₂ ++ w₃ ++ w₄` read from `b`, if `φ`
vanishes along `w₁`, `ψ` vanishes along `w₂`, `φ` is constantly `a` along `w₃` and `ψ`
is constantly `c` along `w₄`, then the integral of `φ dψ` is `2 a c`. -/
theorem wordSum_quadrangle (f : α → Q) (φ ψ : Q → ℤ) (b : Q)
    (w₁ w₂ w₃ w₄ : List (α × Bool)) (a c : ℤ)
    (h₁ : ∀ q ∈ pathPoints f b w₁, φ q = 0)
    (h₂ : ∀ q ∈ pathPoints f (b * wordVal f w₁) w₂, ψ q = 0)
    (h₃ : ∀ q ∈ pathPoints f (b * wordVal f (w₁ ++ w₂)) w₃, φ q = a)
    (h₄ : ∀ q ∈ pathPoints f (b * wordVal f (w₁ ++ w₂ ++ w₃)) w₄, ψ q = c) :
    wordSum f φ ψ b (w₁ ++ w₂ ++ w₃ ++ w₄) = 2 * a * c := by
  rw [wordSum_append, wordSum_append, wordSum_append,
    wordSum_eq_zero_of_phi_zero f φ ψ b w₁ h₁,
    wordSum_eq_zero_of_psi_const f φ ψ _ w₂ 0 h₂,
    wordSum_eq_of_phi_const f φ ψ _ w₃ a h₃,
    wordSum_eq_zero_of_psi_const f φ ψ _ w₄ c h₄]
  have hstart : ψ (b * wordVal f (w₁ ++ w₂)) = 0 := by
    apply h₂
    rw [wordVal_append, ← mul_assoc]
    exact end_mem_pathPoints f _ w₂
  have hend : ψ (b * wordVal f (w₁ ++ w₂) * wordVal f w₃) = c := by
    apply h₄
    rw [wordVal_append f (w₁ ++ w₂) w₃, ← mul_assoc]
    exact start_mem_pathPoints f _ w₄
  rw [hstart, hend]
  ring

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.mem_pathPoints_append
#audit_axioms GroupApproximation.DiscreteStokes.wordSum_eq_of_phi_const
#audit_axioms GroupApproximation.DiscreteStokes.wordSum_quadrangle
