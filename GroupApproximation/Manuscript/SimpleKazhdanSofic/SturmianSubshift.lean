import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import GroupApproximation.Dynamics.SubshiftWordGraph
import GroupApproximation.Meta.AxiomGuard

/-!
# The Sturmian subshift of an irrational slope

`simple_kazhdan_sofic_group.tex` (origin/main bf961c128), section "Every word-problem degree",
tex l.250–256:

> Now use the infinite minimal Sturmian subshift of an irrational slope $\alpha\in(0,1)$
> [MorseHedlund]. Its language is computable from $\alpha$: words of length $n$ are determined by
> the cyclic order of the distinct rotation endpoints $-j\alpha \bmod 1$, $0\le j\le n$.
> Conversely, the minimum number of $1$'s in a word of length $n$ is $\lfloor n\alpha\rfloor$, so
> the language computes $\alpha$.

This module fixes the objects and states the three printed facts as named propositions.
* `sturmianCoding α θ`: the coding of the rotation by `α` from `θ`. Position `n` reads `1`
  exactly when `θ + nα` lies in `[1 - α, 1)` modulo `1`, which is
  `⌊θ + (n + 1)α⌋ - ⌊θ + nα⌋` (`sturmianCoding_eq_floor_sub`).
* `sturmianSubshift α : Subshift Bool ℤ`: the configurations all of whose central windows are
  windows of codings. That is the closure of the codings.
* `PrintedSturmianSubshiftInfiniteMinimal` (tex l.250–251),
  `PrintedSturmianEndpointsDetermineWords` (tex l.251–253, the combinatorial content; computability
  is lane skf-degrees'), `PrintedSturmianMinimumOnes` (tex l.254–255).

Morse–Hedlund is not assumed anywhere: the propositions are proved in
`SturmianSubshiftMinimal` and `SturmianLanguage`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics SymbolicDynamics.FullShift

/-- The coding of the rotation by `α` started at `θ`: position `n` reads `1` exactly when the
rotated point `θ + nα` lies in the arc `[1 - α, 1)` modulo `1`. -/
noncomputable def sturmianCoding (α θ : ℝ) : ℤ → Bool :=
  fun n => decide (1 - α ≤ Int.fract (θ + (n : ℝ) * α))

theorem sturmianCoding_apply (α θ : ℝ) (n : ℤ) :
    sturmianCoding α θ n = decide (1 - α ≤ Int.fract (θ + (n : ℝ) * α)) :=
  rfl

/-- Shifting a coding by `k` starts the rotation `k` steps later. -/
theorem shift_sturmianCoding (α θ : ℝ) (k : ℤ) :
    shift k (sturmianCoding α θ) = sturmianCoding α (θ + (k : ℝ) * α) := by
  funext i
  have h : θ + ((k + i : ℤ) : ℝ) * α = θ + (k : ℝ) * α + (i : ℝ) * α := by
    push_cast
    ring
  simp only [shift_apply, sturmianCoding_apply, h]

/-- A coding only depends on the starting point modulo `1`. -/
theorem sturmianCoding_add_intCast (α θ : ℝ) (z : ℤ) :
    sturmianCoding α (θ + (z : ℝ)) = sturmianCoding α θ := by
  funext i
  have h : θ + (z : ℝ) + (i : ℝ) * α = θ + (i : ℝ) * α + (z : ℝ) := by ring
  simp only [sturmianCoding_apply, h, Int.fract_add_intCast]

/-- For `0 < α < 1`, the letter at position `n` is `⌊θ + (n + 1)α⌋ - ⌊θ + nα⌋`. -/
theorem sturmianCoding_eq_floor_sub (α θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (n : ℤ) :
    (if sturmianCoding α θ n then (1 : ℤ) else 0) =
      ⌊θ + ((n : ℝ) + 1) * α⌋ - ⌊θ + (n : ℝ) * α⌋ := by
  have h1 : θ + ((n : ℝ) + 1) * α =
      (⌊θ + (n : ℝ) * α⌋ : ℝ) + (Int.fract (θ + (n : ℝ) * α) + α) := by
    have := Int.floor_add_fract (θ + (n : ℝ) * α)
    linarith
  rw [h1, Int.floor_intCast_add, add_sub_cancel_left]
  have hlt := Int.fract_lt_one (θ + (n : ℝ) * α)
  have hnn := Int.fract_nonneg (θ + (n : ℝ) * α)
  by_cases h : 1 - α ≤ Int.fract (θ + (n : ℝ) * α)
  · rw [if_pos (by simpa [sturmianCoding_apply] using h)]
    symm
    rw [Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  · rw [if_neg (by simpa [sturmianCoding_apply] using h)]
    symm
    rw [Int.floor_eq_iff]
    have h' : Int.fract (θ + (n : ℝ) * α) < 1 - α := lt_of_not_ge h
    constructor <;> push_cast <;> linarith

/-- The number of `1`'s in the first `n` letters of a coding telescopes. -/
theorem sum_sturmianCoding (α θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, (if sturmianCoding α θ (i : ℤ) then (1 : ℤ) else 0) =
      ⌊θ + (n : ℝ) * α⌋ - ⌊θ⌋ := by
  have key : ∀ i : ℕ, (if sturmianCoding α θ (i : ℤ) then (1 : ℤ) else 0) =
      ⌊θ + ((i + 1 : ℕ) : ℝ) * α⌋ - ⌊θ + ((i : ℕ) : ℝ) * α⌋ := by
    intro i
    have h := sturmianCoding_eq_floor_sub α θ hα0 hα1 (i : ℤ)
    push_cast at h ⊢
    exact h
  rw [Finset.sum_congr rfl fun i _ => key i,
    Finset.sum_range_sub (fun i : ℕ => ⌊θ + ((i : ℕ) : ℝ) * α⌋) n]
  simp only [Nat.cast_zero, zero_mul, add_zero]

/-- The configurations each of whose central windows is a window of a coding. -/
def sturmianCarrier (α : ℝ) : Set (ℤ → Bool) :=
  {x | ∀ N : ℕ, ∃ θ : ℝ, ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → x i = sturmianCoding α θ i}

theorem sturmianCoding_mem_carrier (α θ : ℝ) : sturmianCoding α θ ∈ sturmianCarrier α :=
  fun _ => ⟨θ, fun _ _ _ => rfl⟩

/-- A finite set of integers lies in a symmetric interval. -/
theorem exists_bound_of_finset (I : Finset ℤ) : ∃ N : ℕ, ∀ i ∈ I, -(N : ℤ) ≤ i ∧ i ≤ N := by
  refine ⟨I.sup Int.natAbs, fun i hi => ?_⟩
  have h : i.natAbs ≤ I.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hi
  have hc : ((i.natAbs : ℕ) : ℤ) ≤ ((I.sup Int.natAbs : ℕ) : ℤ) := by exact_mod_cast h
  rcases Int.natAbs_eq i with h' | h' <;> constructor <;> omega

theorem isClosed_sturmianCarrier (α : ℝ) : IsClosed (sturmianCarrier α) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [Set.mem_compl_iff] at hx
  have hN : ∃ N : ℕ, ∀ θ : ℝ, ¬ ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → x i = sturmianCoding α θ i := by
    by_contra h
    refine hx ?_
    show ∀ N : ℕ, ∃ θ : ℝ, ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → x i = sturmianCoding α θ i
    intro N
    by_contra h'
    exact h ⟨N, fun θ hθ => h' ⟨θ, hθ⟩⟩
  obtain ⟨N, hN⟩ := hN
  refine ⟨cylinder (Finset.Icc (-(N : ℤ)) N) x, ?_, isOpen_cylinder _ _, fun _ _ => rfl⟩
  intro y hy
  rw [Set.mem_compl_iff]
  intro hyC
  have hyC' : ∀ N : ℕ, ∃ θ : ℝ, ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → y i = sturmianCoding α θ i := hyC
  obtain ⟨θ, hθ⟩ := hyC' N
  exact hN θ fun i hi1 hi2 =>
    (hy i (Finset.mem_Icc.mpr ⟨hi1, hi2⟩)).symm.trans (hθ i hi1 hi2)

theorem mapsTo_shift_sturmianCarrier (α : ℝ) (k : ℤ) :
    Set.MapsTo (shift k) (sturmianCarrier α) (sturmianCarrier α) := by
  intro x hx
  have hx' : ∀ N : ℕ, ∃ θ : ℝ, ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → x i = sturmianCoding α θ i := hx
  show ∀ N : ℕ, ∃ θ : ℝ, ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → shift k x i = sturmianCoding α θ i
  intro N
  obtain ⟨θ, hθ⟩ := hx' (N + k.natAbs)
  refine ⟨θ + (k : ℝ) * α, fun i hi1 hi2 => ?_⟩
  rw [shift_apply, ← shift_sturmianCoding, shift_apply]
  have hc : ((N + k.natAbs : ℕ) : ℤ) = (N : ℤ) + (k.natAbs : ℤ) := Nat.cast_add N k.natAbs
  exact hθ (k + i) (by rcases Int.natAbs_eq k with h | h <;> omega)
    (by rcases Int.natAbs_eq k with h | h <;> omega)

/-- The Sturmian subshift of slope `α`, as a Mathlib `Subshift`. -/
def sturmianSubshift (α : ℝ) : Subshift Bool ℤ where
  carrier := sturmianCarrier α
  isClosed := isClosed_sturmianCarrier α
  mapsTo := mapsTo_shift_sturmianCarrier α

/-- A subshift over `ℤ` is **minimal** if its only nonempty closed shift-invariant subset is the
whole subshift. -/
def IsMinimalSubshift {A : Type*} [TopologicalSpace A] (S : Subshift A ℤ) : Prop :=
  ∀ Y : Set (ℤ → A), Y ⊆ S.carrier → IsClosed Y → (∀ n : ℤ, Set.MapsTo (shift n) Y Y) →
    Y.Nonempty → Y = S.carrier

/-- Tex l.250–251: for irrational `α ∈ (0,1)`, the Sturmian subshift is infinite and minimal. -/
def PrintedSturmianSubshiftInfiniteMinimal : Prop :=
  ∀ α : ℝ, Irrational α → 0 < α → α < 1 →
    (sturmianSubshift α).carrier.Infinite ∧ IsMinimalSubshift (sturmianSubshift α)

/-- Tex l.251–253, combinatorial content: the rotation endpoints `-jα mod 1`, `0 ≤ j ≤ n`, are
distinct; the word of length `n` read from a coding depends only on the position of the starting
point relative to these endpoints; and these are exactly the words of length `n` of the
subshift. -/
def PrintedSturmianEndpointsDetermineWords : Prop :=
  ∀ α : ℝ, Irrational α → 0 < α → α < 1 → ∀ n : ℕ,
    (∀ i j : ℕ, i ≤ n → j ≤ n → i ≠ j →
        Int.fract (-((i : ℝ) * α)) ≠ Int.fract (-((j : ℝ) * α))) ∧
    (∀ θ θ' : ℝ, (∀ j : ℕ, j ≤ n →
        (Int.fract (-((j : ℝ) * α)) ≤ Int.fract θ ↔ Int.fract (-((j : ℝ) * α)) ≤ Int.fract θ')) →
      WordGraph.word (sturmianCoding α θ) 0 n = WordGraph.word (sturmianCoding α θ') 0 n) ∧
    WordGraph.language (sturmianSubshift α).carrier n =
      {w | ∃ θ : ℝ, WordGraph.word (sturmianCoding α θ) 0 n = w}

/-- Tex l.254–255: the minimum number of `1`'s in a word of length `n` is `⌊nα⌋`. -/
def PrintedSturmianMinimumOnes : Prop :=
  ∀ α : ℝ, Irrational α → 0 < α → α < 1 → ∀ n : ℕ,
    (∀ w ∈ WordGraph.language (sturmianSubshift α).carrier n,
        ⌊(n : ℝ) * α⌋ ≤ ∑ j : Fin n, (if w j then (1 : ℤ) else 0)) ∧
      ∃ w ∈ WordGraph.language (sturmianSubshift α).carrier n,
        ∑ j : Fin n, (if w j then (1 : ℤ) else 0) = ⌊(n : ℝ) * α⌋

#audit_axioms shift_sturmianCoding
#audit_axioms sturmianCoding_add_intCast
#audit_axioms sturmianCoding_eq_floor_sub
#audit_axioms sum_sturmianCoding
#audit_axioms isClosed_sturmianCarrier
#audit_axioms mapsTo_shift_sturmianCarrier

end SimpleKazhdanSofic
end GroupApproximation
