import Mathlib.Algebra.BigOperators.Fin
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianSubshift
import GroupApproximation.Meta.AxiomGuard

/-!
# Words of the Sturmian subshift

`simple_kazhdan_sofic_group.tex` (origin/main e80dcf20a), tex l.264–270:

> So $c(\theta)_t=1$ if and only if $\theta$ lies in the arc $[-(t+1)\alpha,-t\alpha)$ modulo
> $1$, and the words of length $n$ of $X_\alpha$ are the constant values of $c(\theta)_{[0,n)}$ on
> the arcs between the points $-j\alpha\bmod1$, $0\le j\le n$. [...] Since
> $c(\theta)_t=\lfloor\theta+(t+1)\alpha\rfloor-\lfloor\theta+t\alpha\rfloor$, the word
> $c(\theta)_{[0,n)}$ has $\lfloor\theta+n\alpha\rfloor$ ones, within $1$ of $n\alpha$.

* `sturmianCoding_eq_true_iff_arc`: the arc description of a letter.
* `language_sturmianSubshift`: the words of length `n` of the subshift are the words of codings.
* `fract_neg_mul_ne`: the endpoints `-jα mod 1` are distinct.
* `sturmianCoding_eq_true_iff`: a letter is read off from the position of `θ mod 1` relative to
  two consecutive endpoints; `sturmianCoding_word_eq_of_endpoints`: so the word is constant
  between the endpoints.
* `count_word_sturmianCoding`: the number of ones telescopes.
* Closed endpoints `printedSturmianCodingArc`, `printedSturmianEndpointsDetermineWords`,
  `printedSturmianOnesWithinOne`.

The computability sentences ("α computes L(X_α)", "L(X_α) computes α") are lane skf-degrees'.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics SymbolicDynamics.FullShift

/-- `c(θ)_t = 1` exactly on the arc `[-(t+1)α, -tα)` modulo `1`. -/
theorem sturmianCoding_eq_true_iff_arc (α θ : ℝ) (_hα0 : 0 < α) (hα1 : α < 1) (t : ℤ) :
    sturmianCoding α θ t = true ↔
      ∃ z : ℤ, -(((t : ℝ) + 1) * α) + (z : ℝ) ≤ θ ∧ θ < -((t : ℝ) * α) + (z : ℝ) := by
  rw [sturmianCoding_apply, decide_eq_true_eq]
  have hsplit := Int.floor_add_fract (θ + (t : ℝ) * α)
  have hlt := Int.fract_lt_one (θ + (t : ℝ) * α)
  constructor
  · intro h
    refine ⟨⌊θ + (t : ℝ) * α⌋ + 1, ?_, ?_⟩ <;> push_cast <;> linarith
  · rintro ⟨z, hz1, hz2⟩
    have hv : Int.fract (θ + (t : ℝ) * α) = θ + (t : ℝ) * α - ((z - 1 : ℤ) : ℝ) := by
      rw [Int.fract_eq_iff]
      refine ⟨by push_cast; linarith, by push_cast; linarith, z - 1, by ring⟩
    rw [hv]
    push_cast
    linarith

/-- The words of length `n` of the Sturmian subshift are the words read from codings. -/
theorem language_sturmianSubshift (α : ℝ) (n : ℕ) :
    WordGraph.language (sturmianSubshift α).carrier n =
      {w | ∃ θ : ℝ, WordGraph.word (sturmianCoding α θ) 0 n = w} := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ∀ N : ℕ, ∃ θ : ℝ, ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → x i = sturmianCoding α θ i :=
      hx
    obtain ⟨θ, hθ⟩ := hx' n
    rw [Set.mem_setOf_eq]
    refine ⟨θ, ?_⟩
    funext j
    simp only [WordGraph.word_apply, zero_add]
    have hj : (j : ℕ) < n := j.2
    exact (hθ _ (by omega) (by omega)).symm
  · rintro ⟨θ, rfl⟩
    exact WordGraph.word_mem_language (sturmianSubshift α).mapsTo (sturmianCoding_mem_carrier α θ)
      0 n

/-- The rotation endpoints `-jα mod 1` are pairwise distinct. -/
theorem fract_neg_mul_ne (α : ℝ) (hα : Irrational α) (i j : ℕ) (hij : i ≠ j) :
    Int.fract (-((i : ℝ) * α)) ≠ Int.fract (-((j : ℝ) * α)) := by
  intro h
  have hi := Int.floor_add_fract (-((i : ℝ) * α))
  have hj := Int.floor_add_fract (-((j : ℝ) * α))
  have hirr : Irrational ((((j : ℤ) - (i : ℤ) : ℤ) : ℝ) * α) := hα.intCast_mul (by omega)
  apply hirr.ne_int (⌊-((i : ℝ) * α)⌋ - ⌊-((j : ℝ) * α)⌋)
  push_cast
  linarith

/-- A letter of a coding, read from the position of `Int.fract θ` relative to the endpoints
`a = -tα mod 1` and `b = -(t+1)α mod 1`. -/
theorem sturmianCoding_eq_true_iff (α θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (t : ℕ) :
    sturmianCoding α θ (t : ℤ) = true ↔
      (α ≤ Int.fract (-((t : ℝ) * α)) ∧ Int.fract (-(((t + 1 : ℕ) : ℝ) * α)) ≤ Int.fract θ ∧
          Int.fract θ < Int.fract (-((t : ℝ) * α))) ∨
        (Int.fract (-((t : ℝ) * α)) < α ∧ (Int.fract θ < Int.fract (-((t : ℝ) * α)) ∨
          Int.fract (-(((t + 1 : ℕ) : ℝ) * α)) ≤ Int.fract θ)) := by
  have hs0 := Int.fract_nonneg θ
  have hs1 := Int.fract_lt_one θ
  have ha0 := Int.fract_nonneg (-((t : ℝ) * α))
  have ha1 := Int.fract_lt_one (-((t : ℝ) * α))
  have hθs := Int.floor_add_fract θ
  have has := Int.floor_add_fract (-((t : ℝ) * α))
  have hrot : Int.fract (θ + ((t : ℤ) : ℝ) * α) =
      Int.fract (Int.fract θ - Int.fract (-((t : ℝ) * α))) := by
    have e : θ + ((t : ℤ) : ℝ) * α = (Int.fract θ - Int.fract (-((t : ℝ) * α))) +
        ((⌊θ⌋ - ⌊-((t : ℝ) * α)⌋ : ℤ) : ℝ) := by
      push_cast
      linarith
    rw [e, Int.fract_add_intCast]
  rw [sturmianCoding_apply, decide_eq_true_eq, hrot]
  by_cases hat : α ≤ Int.fract (-((t : ℝ) * α))
  · have hb : Int.fract (-(((t + 1 : ℕ) : ℝ) * α)) = Int.fract (-((t : ℝ) * α)) - α := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, ⌊-((t : ℝ) * α)⌋, ?_⟩
      push_cast
      linarith
    rw [hb]
    by_cases has' : Int.fract (-((t : ℝ) * α)) ≤ Int.fract θ
    · have hv : Int.fract (Int.fract θ - Int.fract (-((t : ℝ) * α))) =
          Int.fract θ - Int.fract (-((t : ℝ) * α)) := by
        rw [Int.fract_eq_iff]
        exact ⟨by linarith, by linarith, 0, by simp⟩
      rw [hv]
      constructor
      · intro h
        exfalso
        linarith
      · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
        · linarith
        · linarith
    · have hlt : Int.fract θ < Int.fract (-((t : ℝ) * α)) := lt_of_not_ge has'
      have hv : Int.fract (Int.fract θ - Int.fract (-((t : ℝ) * α))) =
          Int.fract θ - Int.fract (-((t : ℝ) * α)) + 1 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, -1, ?_⟩
        push_cast
        ring
      rw [hv]
      constructor
      · intro h
        exact Or.inl ⟨hat, by linarith, hlt⟩
      · rintro (⟨-, h, -⟩ | ⟨h, -⟩)
        · linarith
        · linarith
  · have hat' : Int.fract (-((t : ℝ) * α)) < α := lt_of_not_ge hat
    have hb : Int.fract (-(((t + 1 : ℕ) : ℝ) * α)) = Int.fract (-((t : ℝ) * α)) - α + 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, ⌊-((t : ℝ) * α)⌋ - 1, ?_⟩
      push_cast
      linarith
    rw [hb]
    by_cases has' : Int.fract (-((t : ℝ) * α)) ≤ Int.fract θ
    · have hv : Int.fract (Int.fract θ - Int.fract (-((t : ℝ) * α))) =
          Int.fract θ - Int.fract (-((t : ℝ) * α)) := by
        rw [Int.fract_eq_iff]
        exact ⟨by linarith, by linarith, 0, by simp⟩
      rw [hv]
      constructor
      · intro h
        exact Or.inr ⟨hat', Or.inr (by linarith)⟩
      · rintro (⟨h, -⟩ | ⟨-, h | h⟩)
        · linarith
        · linarith
        · linarith
    · have hlt : Int.fract θ < Int.fract (-((t : ℝ) * α)) := lt_of_not_ge has'
      have hv : Int.fract (Int.fract θ - Int.fract (-((t : ℝ) * α))) =
          Int.fract θ - Int.fract (-((t : ℝ) * α)) + 1 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, -1, ?_⟩
        push_cast
        ring
      rw [hv]
      constructor
      · intro _
        exact Or.inr ⟨hat', Or.inl hlt⟩
      · intro _
        linarith

/-- The word of length `n` read from a coding is constant between the endpoints `-jα mod 1`,
`0 ≤ j ≤ n`: it depends only on the position of `θ mod 1` relative to them. -/
theorem sturmianCoding_word_eq_of_endpoints (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ)
    (θ θ' : ℝ)
    (h : ∀ j : ℕ, j ≤ n →
      (Int.fract (-((j : ℝ) * α)) ≤ Int.fract θ ↔ Int.fract (-((j : ℝ) * α)) ≤ Int.fract θ')) :
    WordGraph.word (sturmianCoding α θ) 0 n = WordGraph.word (sturmianCoding α θ') 0 n := by
  funext t
  simp only [WordGraph.word_apply, zero_add]
  have ht1 := h t (le_of_lt t.2)
  have ht2 := h ((t : ℕ) + 1) (Nat.succ_le_of_lt t.2)
  rw [Bool.eq_iff_iff, sturmianCoding_eq_true_iff α θ hα0 hα1 t,
    sturmianCoding_eq_true_iff α θ' hα0 hα1 t]
  have hlt : Int.fract θ < Int.fract (-(((t : ℕ) : ℝ) * α)) ↔
      Int.fract θ' < Int.fract (-(((t : ℕ) : ℝ) * α)) := by
    rw [← not_le, ← not_le, ht1]
  rw [hlt, ht2]

/-- The number of ones in the word of length `n` read from a coding telescopes. -/
theorem count_word_sturmianCoding (α θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    ∑ j : Fin n, (if WordGraph.word (sturmianCoding α θ) 0 n j then (1 : ℤ) else 0) =
      ⌊θ + (n : ℝ) * α⌋ - ⌊θ⌋ := by
  simp only [WordGraph.word_apply, zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if sturmianCoding α θ (i : ℤ) then (1 : ℤ) else 0) n]
  exact sum_sturmianCoding α θ hα0 hα1 n

/-- Tex l.264–265, closed. -/
theorem printedSturmianCodingArc : PrintedSturmianCodingArc :=
  fun α hα0 hα1 θ t => sturmianCoding_eq_true_iff_arc α θ hα0 hα1 t

/-- Tex l.265–267, closed. -/
theorem printedSturmianEndpointsDetermineWords : PrintedSturmianEndpointsDetermineWords :=
  fun α hα hα0 hα1 n =>
    ⟨fun i j _ _ hij => fract_neg_mul_ne α hα i j hij,
      fun θ θ' h => sturmianCoding_word_eq_of_endpoints α hα0 hα1 n θ θ' h,
      language_sturmianSubshift α n⟩

/-- Tex l.268–270, closed. -/
theorem printedSturmianOnesWithinOne : PrintedSturmianOnesWithinOne := by
  intro α hα0 hα1 θ hθ0 hθ1 n
  have hfl : ⌊θ⌋ = 0 := by
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨hθ0, by linarith⟩
  refine ⟨fun t => sturmianCoding_eq_floor_sub α θ hα0 hα1 t, ?_, ?_, ?_⟩
  · rw [count_word_sturmianCoding α θ hα0 hα1 n, hfl, sub_zero]
  · have := Int.sub_one_lt_floor (θ + (n : ℝ) * α)
    linarith
  · have := Int.floor_le (θ + (n : ℝ) * α)
    linarith

#audit_axioms sturmianCoding_eq_true_iff_arc
#audit_axioms language_sturmianSubshift
#audit_axioms fract_neg_mul_ne
#audit_axioms sturmianCoding_eq_true_iff
#audit_axioms sturmianCoding_word_eq_of_endpoints
#audit_axioms count_word_sturmianCoding
#audit_closed_axioms printedSturmianCodingArc
#audit_closed_axioms printedSturmianEndpointsDetermineWords
#audit_closed_axioms printedSturmianOnesWithinOne

end SimpleKazhdanSofic
end GroupApproximation
