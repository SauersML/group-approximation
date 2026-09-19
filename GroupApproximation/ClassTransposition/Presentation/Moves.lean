import GroupApproximation.ClassTransposition.Presentation.Frac

/-!
# Moves on ordered box partitions

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1).

A *move* either splits the `i`-th box of an ordered list of boxes into its `p` children
(`splitAt`), or swaps the boxes at `k` and `k + 1` (`swapAt`). A word of moves acts on a list by
`real`, first letter first. Moves preserve ordered partitions (`isPart_real`). Canonical
correspondences between two lists are transported along a word (`forall₂_real`), so `frac`
commutes with realization.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

/-- The `p` children of `E`, in order. -/
def kids (E : Box) (p : ℕ) : List Box := (List.finRange p).map fun j => place E (child p j)

@[simp] theorem length_kids (E : Box) (p : ℕ) : (kids E p).length = p := by simp [kids]

/-- Split the `i`-th box by `p`. -/
def splitAt : List Box → ℕ → ℕ → List Box
  | [], _, _ => []
  | E :: b, 0, p => kids E p ++ b
  | E :: b, i + 1, p => E :: splitAt b i p

/-- Swap the entries at `k` and `k + 1`. -/
def swapAt {α : Type*} : List α → ℕ → List α
  | E :: b, k + 1 => E :: swapAt b k
  | E :: F :: b, 0 => F :: E :: b
  | b, _ => b

@[simp] theorem swapAt_zero {α : Type*} (E F : α) (b : List α) :
    swapAt (E :: F :: b) 0 = F :: E :: b := rfl

@[simp] theorem swapAt_succ {α : Type*} (E : α) (b : List α) (k : ℕ) :
    swapAt (E :: b) (k + 1) = E :: swapAt b k := rfl

theorem swapAt_perm {α : Type*} : ∀ (b : List α) (k : ℕ), (swapAt b k).Perm b
  | [], _ => List.Perm.refl _
  | [_], 0 => List.Perm.refl _
  | _ :: _ :: _, 0 => List.Perm.swap _ _ _
  | E :: b, k + 1 => (swapAt_perm b k).cons E

@[simp] theorem length_swapAt {α : Type*} (b : List α) (k : ℕ) :
    (swapAt b k).length = b.length :=
  (swapAt_perm b k).length_eq

theorem length_splitAt : ∀ (b : List Box) (i p : ℕ), i < b.length →
    (splitAt b i p).length = b.length + p - 1
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | E :: b, 0, p, _ => by
    simp only [splitAt, List.length_append, length_kids, List.length_cons]; omega
  | E :: b, i + 1, p, h => by
    simp only [splitAt, List.length_cons]
    rw [length_splitAt b i p (by simpa using h)]
    simp at h
    omega

/-! ### Partitions are preserved -/

theorem kids_sub {E : Box} {p : ℕ} : ∀ X ∈ kids E p, ∀ n, X.Mem n → E.Mem n := by
  intro X hX n hn
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hX
  exact place_mem_of hn

theorem kids_pairwise (E : Box) (p : ℕ) : (kids E p).Pairwise Box.Disj := by
  unfold kids
  rw [List.pairwise_map]
  exact (List.nodup_finRange p).pairwise_of_forall_ne fun i _ j _ hij =>
    disj_place (child_disj p hij)

theorem kids_cover {E : Box} {p : ℕ} (hp : 0 < p) {n : ℤ} (hn : E.Mem n) :
    ∃ X ∈ kids E p, X.Mem n :=
  ⟨_, List.mem_map.2 ⟨classOf p hp (n / E.m), List.mem_finRange _, rfl⟩,
    mem_place.2 ⟨hn, mem_classOf p hp _⟩⟩

theorem splitAt_sub : ∀ (b : List Box) (i p : ℕ), ∀ X ∈ splitAt b i p,
    ∃ Y ∈ b, ∀ n, X.Mem n → Y.Mem n
  | [], _, _, X, h => by simp [splitAt] at h
  | E :: b, 0, p, X, h => by
    rcases List.mem_append.1 h with h | h
    · exact ⟨E, List.mem_cons_self, kids_sub X h⟩
    · exact ⟨X, List.mem_cons_of_mem _ h, fun _ hn => hn⟩
  | E :: b, i + 1, p, X, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨X, List.mem_cons_self, fun _ hn => hn⟩
    · obtain ⟨Y, hY, hXY⟩ := splitAt_sub b i p X h
      exact ⟨Y, List.mem_cons_of_mem _ hY, hXY⟩

theorem splitAt_cover {p : ℕ} (hp : 0 < p) : ∀ (b : List Box) (i : ℕ), ∀ Y ∈ b, ∀ n, Y.Mem n →
    ∃ X ∈ splitAt b i p, X.Mem n
  | [], _, Y, h, _, _ => by simp at h
  | E :: b, 0, Y, h, n, hn => by
    rcases List.mem_cons.1 h with rfl | h
    · obtain ⟨X, hX, hXn⟩ := kids_cover hp hn
      exact ⟨X, List.mem_append_left _ hX, hXn⟩
    · exact ⟨Y, List.mem_append_right _ h, hn⟩
  | E :: b, i + 1, Y, h, n, hn => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨Y, List.mem_cons_self, hn⟩
    · obtain ⟨X, hX, hXn⟩ := splitAt_cover hp b i Y h n hn
      exact ⟨X, List.mem_cons_of_mem _ hX, hXn⟩

theorem splitAt_pairwise : ∀ (b : List Box) (i p : ℕ), b.Pairwise Box.Disj →
    (splitAt b i p).Pairwise Box.Disj
  | [], _, _, _ => List.Pairwise.nil
  | E :: b, 0, p, h => by
    rw [List.pairwise_cons] at h
    refine List.pairwise_append.2 ⟨kids_pairwise E p, h.2, fun X hX Y hY n hx hy => ?_⟩
    exact h.1 Y hY n (kids_sub X hX n hx) hy
  | E :: b, i + 1, p, h => by
    show List.Pairwise Box.Disj (E :: splitAt b i p)
    rw [List.pairwise_cons] at h ⊢
    refine ⟨fun X hX n he hx => ?_, splitAt_pairwise b i p h.2⟩
    obtain ⟨Y, hY, hXY⟩ := splitAt_sub b i p X hX
    exact h.1 Y hY n he (hXY n hx)

theorem isPart_splitAt {b : List Box} (hb : IsPart b) (i : ℕ) {p : ℕ} (hp : 0 < p) :
    IsPart (splitAt b i p) := by
  refine ⟨splitAt_pairwise b i p hb.1, fun n => ?_⟩
  obtain ⟨Y, hY, hn⟩ := hb.2 n
  exact splitAt_cover hp b i Y hY n hn

theorem isPart_swapAt {b : List Box} (hb : IsPart b) (k : ℕ) : IsPart (swapAt b k) := by
  have hp := swapAt_perm b k
  refine ⟨(hp.pairwise_iff fun h => h.symm).2 hb.1, fun n => ?_⟩
  obtain ⟨Y, hY, hn⟩ := hb.2 n
  exact ⟨Y, hp.mem_iff.2 hY, hn⟩

/-! ### Transport of canonical correspondences -/

theorem forall₂_append' {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List α} {l₄ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R l₃ l₄ → List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (forall₂_append' t h')

theorem forall₂_kids {g : Perm ℤ} {E F : Box} (hg : CanonOn g E F) (p : ℕ) :
    List.Forall₂ (CanonOn g) (kids E p) (kids F p) := by
  have h := forall₂_canon_map hg ((List.finRange p).map (child p))
  simpa only [kids, List.map_map, Function.comp_def] using h

theorem forall₂_splitAt {g : Perm ℤ} : ∀ {b c : List Box}, List.Forall₂ (CanonOn g) b c →
    ∀ i p, List.Forall₂ (CanonOn g) (splitAt b i p) (splitAt c i p)
  | _, _, .nil, _, _ => .nil
  | _, _, .cons h t, 0, p => forall₂_append' (forall₂_kids h p) t
  | _, _, .cons h t, i + 1, p => .cons h (forall₂_splitAt t i p)

theorem forall₂_swapAt {α β : Type*} {R : α → β → Prop} : ∀ {b : List α} {c : List β},
    List.Forall₂ R b c → ∀ k, List.Forall₂ R (swapAt b k) (swapAt c k)
  | _, _, .nil, _ => .nil
  | _, _, .cons h .nil, 0 => .cons h .nil
  | _, _, .cons h (.cons h' t), 0 => .cons h' (.cons h t)
  | _, _, .cons h t, k + 1 => .cons h (forall₂_swapAt t k)

/-! ### Words of moves -/

/-- A move: split box `i` by `p`, or swap boxes `k` and `k + 1`. -/
inductive Move
  | split (i p : ℕ)
  | swap (k : ℕ)
  deriving DecidableEq

/-- Apply a move to a list of boxes. -/
def Move.app (b : List Box) : Move → List Box
  | .split i p => splitAt b i p
  | .swap k => swapAt b k

/-- Every split in the move has a positive arity. -/
def Move.Ok : Move → Prop
  | .split _ p => 0 < p
  | .swap _ => True

/-- The realization of a word, first letter first. -/
def real : List Box → List Move → List Box
  | b, [] => b
  | b, m :: w => real (m.app b) w

@[simp] theorem real_nil (b : List Box) : real b [] = b := rfl

@[simp] theorem real_cons (b : List Box) (m : Move) (w : List Move) :
    real b (m :: w) = real (m.app b) w := rfl

theorem real_append : ∀ (b : List Box) (u v : List Move), real b (u ++ v) = real (real b u) v
  | _, [], _ => rfl
  | b, m :: u, v => real_append (m.app b) u v

theorem isPart_app {b : List Box} (hb : IsPart b) {m : Move} (hm : m.Ok) : IsPart (m.app b) := by
  cases m with
  | split i p => exact isPart_splitAt hb i hm
  | swap k => exact isPart_swapAt hb k

theorem isPart_real : ∀ {b : List Box} (_ : IsPart b) (w : List Move), (∀ m ∈ w, m.Ok) →
    IsPart (real b w)
  | _, hb, [], _ => hb
  | _, hb, m :: w, hw => isPart_real (isPart_app hb (hw m List.mem_cons_self)) w
      fun m' hm' => hw m' (List.mem_cons_of_mem _ hm')

theorem forall₂_app {g : Perm ℤ} {b c : List Box} (h : List.Forall₂ (CanonOn g) b c) :
    ∀ m : Move, List.Forall₂ (CanonOn g) (m.app b) (m.app c)
  | .split i p => forall₂_splitAt h i p
  | .swap k => forall₂_swapAt h k

theorem forall₂_real {g : Perm ℤ} : ∀ {b c : List Box}, List.Forall₂ (CanonOn g) b c →
    ∀ w : List Move, List.Forall₂ (CanonOn g) (real b w) (real c w)
  | _, _, h, [] => h
  | _, _, h, m :: w => forall₂_real (forall₂_app h m) w

end GroupApproximation.ClassTransposition.Presentation
