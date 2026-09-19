import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

/-!
# Word length and the word metric of a symmetric generating set

Mathlib carries no word metric at this revision, so this module supplies
one.  For an alphabet `S ⊆ G` the *word length* `|g|_S` is the least
length of a list of letters of `S` whose ordered product is `g`, and the
*word metric* is `d_S(x,y) = |x⁻¹y|_S`.

Both are defined for an arbitrary `S` as the infimum of a set of naturals
— so the junk value is `0` when `g` is not a product of letters of `S` —
and the calculus is then developed under `IsSymmetricGeneratingSet S`,
which is exactly the hypothesis making every element representable and
the infimum attained.

This is the object written `|\gamma|_S` in Step 3 and Step 4 of the proof
sketch of the involutive collapse theorem `\ref{thm:collapse}` that
`non_mf_groups_exist.tex` printed until commit `3a45fa60`, where the
displacement
bound `d_n(1,\gamma) \le |\gamma|_S\,k_n` and the mass estimate
`\|b_n(\gamma)\|_{\mathrm F}^2 \le 4|\gamma|_S` were both stated against
the *minimum* over representing words, not against the length of some
chosen word.  The collapse-side consequences are in
`GroupApproximation/Sofic/CollapseWordMetric.lean`, whose header records that
the sketch is no longer printed.  The word metric itself is a general-purpose
object and stands independently of that.

The development is deliberately general — `S` need not be finite and need
not contain `1` — so that it is reusable elsewhere in the repository.
-/

namespace GroupApproximation
namespace WordMetric

variable {G : Type*} [Group G]

/-! ## Words -/

/-- `IsWord S l g` records that the list `l` spells `g` in the letters `S`:
every entry of `l` lies in `S`, and the entries multiply, in order, to
`g`. -/
structure IsWord (S : Set G) (l : List G) (g : G) : Prop where
  /-- Every letter of the word lies in the alphabet. -/
  letters : ∀ x ∈ l, x ∈ S
  /-- The word spells the element. -/
  prod_eq : l.prod = g

/-- The empty word spells the identity. -/
theorem isWord_nil (S : Set G) : IsWord S [] 1 :=
  ⟨by simp, List.prod_nil⟩

/-- A single letter spells itself. -/
theorem isWord_singleton {S : Set G} {g : G} (hg : g ∈ S) : IsWord S [g] g := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_singleton.mp hx with rfl
    exact hg
  · simp

/-- Concatenating words spells the product. -/
theorem isWord_append {S : Set G} {l₁ l₂ : List G} {g₁ g₂ : G}
    (h₁ : IsWord S l₁ g₁) (h₂ : IsWord S l₂ g₂) :
    IsWord S (l₁ ++ l₂) (g₁ * g₂) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact h₁.letters x hx'
    · exact h₂.letters x hx'
  · rw [List.prod_append, h₁.prod_eq, h₂.prod_eq]

/-- Reversing a word and inverting each letter spells the inverse.  This is
the one place where symmetry of the alphabet is used. -/
theorem isWord_inv {S : Set G} (hsymm : ∀ x ∈ S, x⁻¹ ∈ S) {l : List G} {g : G}
    (h : IsWord S l g) : IsWord S ((l.map fun y ↦ y⁻¹).reverse) g⁻¹ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_reverse, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hsymm y (h.letters y hy)
  · rw [← List.prod_inv_reverse, h.prod_eq]

/-! ## The word length -/

/-- The set of lengths of `S`-words spelling `g`. -/
def wordLengths (S : Set G) (g : G) : Set ℕ :=
  {n : ℕ | ∃ l : List G, IsWord S l g ∧ l.length = n}

/-- Membership in `wordLengths` unfolds to the existence of a word of that
length. -/
theorem mem_wordLengths_iff {S : Set G} {g : G} {n : ℕ} :
    n ∈ wordLengths S g ↔ ∃ l : List G, IsWord S l g ∧ l.length = n :=
  Iff.rfl

/-- The length of any representing word is one of the representable
lengths. -/
theorem length_mem_wordLengths {S : Set G} {l : List G} {g : G}
    (h : IsWord S l g) : l.length ∈ wordLengths S g :=
  ⟨l, h, rfl⟩

/-- The **word length** `|g|_S`: the least length of an `S`-word spelling
`g`, and `0` if there is none. -/
noncomputable def wordNorm (S : Set G) (g : G) : ℕ :=
  sInf (wordLengths S g)

/-- **Minimality.**  Every word spelling `g` is at least as long as
`|g|_S`; equivalently `|g|_S` is a lower bound for representing words. -/
theorem wordNorm_le_length {S : Set G} {l : List G} {g : G}
    (h : IsWord S l g) : wordNorm S g ≤ l.length :=
  Nat.sInf_le (length_mem_wordLengths h)

/-- `|1|_S = 0`, with no hypothesis on the alphabet. -/
theorem wordNorm_one (S : Set G) : wordNorm S 1 = 0 := by
  have h : wordNorm S 1 ≤ ([] : List G).length :=
    wordNorm_le_length (isWord_nil S)
  rw [List.length_nil] at h
  omega

/-- A letter has word length at most one. -/
theorem wordNorm_le_one_of_mem {S : Set G} {g : G} (hg : g ∈ S) :
    wordNorm S g ≤ 1 := by
  have h : wordNorm S g ≤ ([g] : List G).length :=
    wordNorm_le_length (isWord_singleton hg)
  simpa using h

/-! ## Symmetric generating sets -/

/-- A **symmetric generating set**: an alphabet closed under inversion that
generates the whole group.  This is exactly the hypothesis under which
every element has a word, so that the infimum defining `wordNorm` is over
a nonempty set and is attained. -/
structure IsSymmetricGeneratingSet (S : Set G) : Prop where
  /-- The alphabet is closed under inversion. -/
  inv_mem : ∀ x ∈ S, x⁻¹ ∈ S
  /-- The alphabet generates the group. -/
  closure_eq : Subgroup.closure S = ⊤

/-- Every element of a group with a symmetric generating set is the ordered
product of a list of letters. -/
theorem exists_isWord {S : Set G} (hS : IsSymmetricGeneratingSet S) (g : G) :
    ∃ l : List G, IsWord S l g := by
  have hmem : g ∈ Subgroup.closure S := by
    rw [hS.closure_eq]
    exact Subgroup.mem_top g
  have hmem' : g ∈ Submonoid.closure (S ∪ S⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid]
    exact hmem
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hmem'
  refine ⟨l, ?_, hprod⟩
  intro x hx
  rcases hl x hx with h | h
  · exact h
  · have hxinv : x⁻¹ ∈ S := by rwa [Set.mem_inv] at h
    have hx' := hS.inv_mem x⁻¹ hxinv
    rwa [inv_inv] at hx'

/-- Over a symmetric generating set every element has some word, so the set
of representable lengths is nonempty. -/
theorem wordLengths_nonempty {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (g : G) : (wordLengths S g).Nonempty := by
  obtain ⟨l, hl⟩ := exists_isWord hS g
  exact ⟨l.length, length_mem_wordLengths hl⟩

/-- **Well-definedness.**  The infimum defining `|g|_S` is attained: there
is an `S`-word for `g` of length exactly `|g|_S`. -/
theorem exists_isWord_length_eq {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (g : G) : ∃ l : List G, IsWord S l g ∧ l.length = wordNorm S g := by
  have h : wordNorm S g ∈ wordLengths S g :=
    Nat.sInf_mem (wordLengths_nonempty hS g)
  exact mem_wordLengths_iff.mp h

/-! ## The length function laws -/

/-- `|g|_S = 0` exactly for the identity. -/
theorem wordNorm_eq_zero_iff {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (g : G) : wordNorm S g = 0 ↔ g = 1 := by
  constructor
  · intro h
    obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS g
    rw [h] at hlen
    have hnil : l = [] := List.length_eq_zero_iff.mp hlen
    rw [← hl.prod_eq, hnil, List.prod_nil]
  · rintro rfl
    exact wordNorm_one S

/-- A nonidentity element has positive word length. -/
theorem one_le_wordNorm {S : Set G} (hS : IsSymmetricGeneratingSet S) {g : G}
    (hg : g ≠ 1) : 1 ≤ wordNorm S g := by
  rcases Nat.eq_zero_or_pos (wordNorm S g) with h | h
  · exact absurd ((wordNorm_eq_zero_iff hS g).mp h) hg
  · exact h

/-- **Subadditivity**: `|xy|_S ≤ |x|_S + |y|_S`. -/
theorem wordNorm_mul_le {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (g₁ g₂ : G) :
    wordNorm S (g₁ * g₂) ≤ wordNorm S g₁ + wordNorm S g₂ := by
  obtain ⟨l₁, h₁, hlen₁⟩ := exists_isWord_length_eq hS g₁
  obtain ⟨l₂, h₂, hlen₂⟩ := exists_isWord_length_eq hS g₂
  have h : wordNorm S (g₁ * g₂) ≤ (l₁ ++ l₂).length :=
    wordNorm_le_length (isWord_append h₁ h₂)
  rw [List.length_append, hlen₁, hlen₂] at h
  exact h

/-- **Inversion invariance**: `|g⁻¹|_S = |g|_S`, using symmetry of `S`. -/
theorem wordNorm_inv {S : Set G} (hS : IsSymmetricGeneratingSet S) (g : G) :
    wordNorm S g⁻¹ = wordNorm S g := by
  have key : ∀ x : G, wordNorm S x⁻¹ ≤ wordNorm S x := by
    intro x
    obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS x
    have h : wordNorm S x⁻¹ ≤ ((l.map fun y ↦ y⁻¹).reverse).length :=
      wordNorm_le_length (isWord_inv hS.inv_mem hl)
    have hlen' : ((l.map fun y ↦ y⁻¹).reverse).length = l.length := by simp
    rw [hlen', hlen] at h
    exact h
  refine le_antisymm (key g) ?_
  have h := key g⁻¹
  rwa [inv_inv] at h

/-- Enlarging the alphabet cannot increase the word length. -/
theorem wordNorm_mono {S T : Set G} (hST : S ⊆ T) {g : G}
    (h : (wordLengths S g).Nonempty) : wordNorm T g ≤ wordNorm S g := by
  have hmem : wordNorm S g ∈ wordLengths S g := Nat.sInf_mem h
  obtain ⟨l, hl, hlen⟩ := mem_wordLengths_iff.mp hmem
  have hlT : IsWord T l g := ⟨fun x hx ↦ hST (hl.letters x hx), hl.prod_eq⟩
  have hle : wordNorm T g ≤ l.length := wordNorm_le_length hlT
  rw [hlen] at hle
  exact hle

/-! ## The word metric -/

/-- The **word metric** `d_S(x,y) = |x⁻¹y|_S`. -/
noncomputable def wordDist (S : Set G) (x y : G) : ℕ :=
  wordNorm S (x⁻¹ * y)

/-- The word metric from the identity is the word length. -/
theorem wordDist_one_left (S : Set G) (g : G) :
    wordDist S 1 g = wordNorm S g := by
  unfold wordDist
  rw [inv_one, one_mul]

/-- Reflexivity. -/
theorem wordDist_self (S : Set G) (x : G) : wordDist S x x = 0 := by
  unfold wordDist
  rw [inv_mul_cancel]
  exact wordNorm_one S

/-- Symmetry of the word metric, from `wordNorm_inv`. -/
theorem wordDist_comm {S : Set G} (hS : IsSymmetricGeneratingSet S) (x y : G) :
    wordDist S x y = wordDist S y x := by
  have h : y⁻¹ * x = (x⁻¹ * y)⁻¹ := by group
  unfold wordDist
  rw [h, wordNorm_inv hS]

/-- The triangle inequality, from subadditivity of the word length. -/
theorem wordDist_triangle {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (x y z : G) : wordDist S x z ≤ wordDist S x y + wordDist S y z := by
  have h : x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) := by group
  unfold wordDist
  rw [h]
  exact wordNorm_mul_le hS _ _

/-- The word metric is invariant under left translation. -/
theorem wordDist_left_invariant (S : Set G) (g x y : G) :
    wordDist S (g * x) (g * y) = wordDist S x y := by
  have h : (g * x)⁻¹ * (g * y) = x⁻¹ * y := by group
  unfold wordDist
  rw [h]

/-- The word metric separates points. -/
theorem wordDist_eq_zero_iff {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (x y : G) : wordDist S x y = 0 ↔ x = y := by
  unfold wordDist
  rw [wordNorm_eq_zero_iff hS, inv_mul_eq_one]

end WordMetric
end GroupApproximation
