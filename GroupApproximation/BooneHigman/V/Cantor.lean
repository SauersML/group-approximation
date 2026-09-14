import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Disjoint

/-!
# The Cantor space of an alphabet: words, streams and cones

For an alphabet `X` with `d` letters, `Cantor X = ℕ → X` is the boundary of the rooted `d`-ary tree,
whose vertices are the finite words `List X`.  This module is the arity-general form of the binary
boundary calculus of `Leavitt/ThompsonV.lean` and `Leavitt/FamilyVEmbedding.lean`, which fix `X = Fin 2`.

* `prepend w x` is the stream `w x`, and `dropN m x` deletes the first `m` letters of `x`;
* `IsStreamPrefix w x` says that `x` begins with `w`, and `cone w` is the set of such streams;
* `firstWord N x` is the word of the first `N` letters, with `prepend (firstWord N x) (dropN N x) = x`;
* comparable words have nested cones (`cone_subset_of_prefix`), incomparable words have disjoint cones
  (`disjoint_cone`), and a word is recovered from the substitution it performs once `X` has two letters
  (`prepend_injective_word`).

Nothing here assumes that `X` is finite; `finite_words_length_eq` counts the words of a fixed length when
it is.
-/

namespace GroupApproximation
namespace BooneHigman

variable {X : Type*}

/-- The boundary of the rooted tree over the alphabet `X`: infinite streams of letters. -/
abbrev Cantor (X : Type*) := ℕ → X

/-- The stream `w x`: the finite word `w` followed by the stream `x`. -/
def prepend (w : List X) (x : Cantor X) : Cantor X := fun n ↦
  if h : n < w.length then w[n] else x (n - w.length)

/-- Delete the first `m` letters of a stream. -/
def dropN (m : ℕ) (x : Cantor X) : Cantor X := fun n ↦ x (n + m)

/-- A finite word is an initial segment of a stream. -/
def IsStreamPrefix (w : List X) (x : Cantor X) : Prop :=
  ∀ k : ℕ, ∀ h : k < w.length, x k = w[k]

/-- The cone of the vertex `w`: the streams beginning with `w`. -/
def cone (w : List X) : Set (Cantor X) := {x | IsStreamPrefix w x}

/-- The word of the first `N` letters of a stream. -/
def firstWord (N : ℕ) (x : Cantor X) : List X := List.ofFn fun i : Fin N ↦ x i

@[simp] theorem mem_cone {w : List X} {x : Cantor X} : x ∈ cone w ↔ IsStreamPrefix w x := Iff.rfl

theorem prepend_getElem (w : List X) (x : Cantor X) {n : ℕ} (hn : n < w.length) :
    prepend w x n = w[n] := by
  rw [prepend, dif_pos hn]

theorem prepend_of_length_le (w : List X) (x : Cantor X) {n : ℕ} (hn : ¬ n < w.length) :
    prepend w x n = x (n - w.length) := by
  rw [prepend, dif_neg hn]

@[simp] theorem prepend_nil (x : Cantor X) : prepend [] x = x := by
  funext n
  simp [prepend]

theorem prepend_append (a b : List X) (x : Cantor X) :
    prepend (a ++ b) x = prepend a (prepend b x) := by
  funext n
  by_cases hn : n < a.length
  · have h1 : n < (a ++ b).length := by
      simp only [List.length_append]; omega
    rw [prepend_getElem _ _ h1, prepend_getElem _ _ hn]
    exact List.getElem_append_left hn
  · rw [prepend_of_length_le _ _ hn]
    by_cases hm : n - a.length < b.length
    · have h1 : n < (a ++ b).length := by
        simp only [List.length_append]; omega
      rw [prepend_getElem _ _ h1, prepend_getElem _ _ hm]
      exact List.getElem_append_right (by omega)
    · have h1 : ¬ n < (a ++ b).length := by
        simp only [List.length_append]; omega
      rw [prepend_of_length_le _ _ h1, prepend_of_length_le _ _ hm]
      congr 1
      simp only [List.length_append]
      omega

theorem isStreamPrefix_prepend (w : List X) (x : Cantor X) : IsStreamPrefix w (prepend w x) := by
  intro k h
  rw [prepend_getElem _ _ h]

theorem prepend_mem_cone (w : List X) (x : Cantor X) : prepend w x ∈ cone w :=
  isStreamPrefix_prepend w x

@[simp] theorem dropN_prepend (w : List X) (x : Cantor X) : dropN w.length (prepend w x) = x := by
  funext n
  simp [dropN, prepend]

theorem prepend_dropN_of_isStreamPrefix (w : List X) (x : Cantor X) (h : IsStreamPrefix w x) :
    prepend w (dropN w.length x) = x := by
  funext n
  by_cases hn : n < w.length
  · rw [prepend_getElem _ _ hn]
    exact (h n hn).symm
  · rw [prepend_of_length_le _ _ hn, dropN]
    congr 1
    omega

theorem mem_cone_iff {w : List X} {x : Cantor X} : x ∈ cone w ↔ ∃ y, x = prepend w y :=
  ⟨fun h ↦ ⟨dropN w.length x, (prepend_dropN_of_isStreamPrefix w x h).symm⟩,
    by rintro ⟨y, rfl⟩; exact isStreamPrefix_prepend w y⟩

theorem prepend_injective (w : List X) : Function.Injective (prepend (X := X) w) := by
  intro x y h
  have h' := congrArg (dropN w.length) h
  rwa [dropN_prepend, dropN_prepend] at h'

@[simp] theorem length_firstWord (N : ℕ) (y : Cantor X) : (firstWord N y).length = N := by
  simp [firstWord]

theorem prepend_firstWord (N : ℕ) (y : Cantor X) : prepend (firstWord N y) (dropN N y) = y := by
  funext n
  by_cases hn : n < N
  · rw [prepend_getElem _ _ (by simpa using hn)]
    simp [firstWord]
  · rw [prepend_of_length_le _ _ (by simpa using hn), length_firstWord]
    show y (n - N + N) = y n
    congr 1
    omega

theorem isStreamPrefix_firstWord (N : ℕ) (y : Cantor X) : IsStreamPrefix (firstWord N y) y := by
  have h := isStreamPrefix_prepend (firstWord N y) (dropN N y)
  rwa [prepend_firstWord] at h

/-- Two initial segments of one stream are comparable words. -/
theorem prefix_or_prefix_of_isStreamPrefix {v w : List X} {x : Cantor X}
    (hv : IsStreamPrefix v x) (hw : IsStreamPrefix w x) : v <+: w ∨ w <+: v := by
  rcases le_total v.length w.length with hle | hle
  · left
    refine List.prefix_iff_getElem.mpr ⟨hle, fun k hk ↦ ?_⟩
    rw [← hv k hk, hw k (lt_of_lt_of_le hk hle)]
  · right
    refine List.prefix_iff_getElem.mpr ⟨hle, fun k hk ↦ ?_⟩
    rw [← hw k hk, hv k (lt_of_lt_of_le hk hle)]

/-- Equal streams with comparable-length prefixes have comparable prefixes. -/
theorem prefix_of_prepend_eq {p q : List X} {a b : Cantor X}
    (h : prepend p a = prepend q b) (hlen : p.length ≤ q.length) : p <+: q := by
  refine List.prefix_iff_getElem.mpr ⟨hlen, fun n hn ↦ ?_⟩
  have hc := congrFun h n
  rwa [prepend_getElem _ _ hn, prepend_getElem _ _ (lt_of_lt_of_le hn hlen)] at hc

theorem IsStreamPrefix.of_prefix {v w : List X} {x : Cantor X} (h : v <+: w)
    (hw : IsStreamPrefix w x) : IsStreamPrefix v x := by
  obtain ⟨hle, hget⟩ := List.prefix_iff_getElem.mp h
  intro k hk
  rw [hw k (lt_of_lt_of_le hk hle)]
  exact (hget k hk).symm

theorem cone_subset_of_prefix {v w : List X} (h : v <+: w) : cone w ⊆ cone v :=
  fun _ hx ↦ IsStreamPrefix.of_prefix h hx

theorem cone_append_subset (v c : List X) : cone (v ++ c) ⊆ cone v :=
  cone_subset_of_prefix (List.prefix_append v c)

/-- Incomparable words have disjoint cones. -/
theorem disjoint_cone {v w : List X} (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    Disjoint (cone v) (cone w) := by
  rw [Set.disjoint_left]
  intro x hv hw
  rcases prefix_or_prefix_of_isStreamPrefix hv hw with h | h
  · exact hvw h
  · exact hwv h

/-- Distinct words of one length have disjoint cones. -/
theorem disjoint_cone_of_length_eq {v w : List X} (hlen : v.length = w.length) (hne : v ≠ w) :
    Disjoint (cone v) (cone w) :=
  disjoint_cone (fun h ↦ hne (h.eq_of_length hlen)) (fun h ↦ hne (h.eq_of_length hlen.symm).symm)

/-- A word of length at most `|u|` whose cone meets `cone u` is a prefix of `u`. -/
theorem prefix_of_isStreamPrefix_of_length_le {w u : List X} {x : Cantor X}
    (hw : IsStreamPrefix w x) (hu : IsStreamPrefix u x) (hlen : w.length ≤ u.length) : w <+: u := by
  rcases prefix_or_prefix_of_isStreamPrefix hw hu with h | h
  · exact h
  · have heq : u = w := h.eq_of_length (le_antisymm h.length_le hlen)
    subst heq
    exact List.prefix_refl _

/-- A word is determined by the substitution it performs, once the alphabet has two letters. -/
theorem prepend_injective_word [Nontrivial X] {v w : List X}
    (h : ∀ x : Cantor X, prepend v x = prepend w x) : v = w := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  have key : ∀ v w : List X, (∀ x : Cantor X, prepend v x = prepend w x) →
      v.length ≤ w.length := by
    intro v w h
    by_contra hle
    have hlt : w.length < v.length := Nat.lt_of_not_le hle
    have h0 := congrFun (h fun _ ↦ a) w.length
    have h1 := congrFun (h fun _ ↦ b) w.length
    rw [prepend_getElem _ _ hlt, prepend_of_length_le _ _ (lt_irrefl _)] at h0 h1
    rw [h0] at h1
    exact hab h1
  have hlen : v.length = w.length :=
    le_antisymm (key v w h) (key w v fun x ↦ (h x).symm)
  apply List.ext_getElem hlen
  intro n h1 h2
  have hc := congrFun (h fun _ ↦ a) n
  rwa [prepend_getElem _ _ h1, prepend_getElem _ _ h2] at hc

/-- The words of a fixed length over a finite alphabet are finite in number. -/
theorem finite_words_length_eq [Finite X] (N : ℕ) : {w : List X | w.length = N}.Finite :=
  List.finite_length_eq X N

end BooneHigman
end GroupApproximation
