import GroupApproximation.ClassTransposition.Presentation.ListId
import GroupApproximation.ClassTransposition.Presentation.Gens

/-!
# Block moves and layers on lists of boxes

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §2).

* `real_bubbleR` and `real_bubbleL`: the swap word `swaps k (range c)` and its reverse move one
  box past a block `c`. They give the naturality relations (d) for a swap followed by a split of
  one of the two swapped boxes (`splitAt_swapAt_self`, `splitAt_swapAt_succ`).
* `real_layer`: a layer of splits of a block, left to right.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

theorem swaps_range_succ (k n : ℕ) :
    swaps k (List.range (n + 1)) = .swap k :: swaps (k + 1) (List.range n) := by
  simp only [swaps, List.range_succ_eq_map, List.map_cons, List.map_map, add_zero]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply]
  congr 1
  omega

theorem swaps_range_succ_reverse (k n : ℕ) :
    swaps k (List.range (n + 1)).reverse = .swap (k + n) :: swaps k (List.range n).reverse := by
  simp [swaps, List.range_succ]

theorem swapAt_mid (l l' : List Box) (E F : Box) :
    swapAt (l ++ E :: F :: l') l.length = l ++ F :: E :: l' := by
  have h := swapAt_append_right l (E :: F :: l') 0
  rwa [add_zero, swapAt_zero] at h

/-- Moving a box to the right past a block. -/
theorem real_bubbleR (E : Box) (l' : List Box) : ∀ (c l : List Box),
    real (l ++ E :: (c ++ l')) (swaps l.length (List.range c.length)) = l ++ c ++ E :: l'
  | [], l => by simp [swaps]
  | x :: c, l => by
    rw [List.length_cons, swaps_range_succ, real_cons]
    have e : Move.app (l ++ E :: (x :: c ++ l')) (.swap l.length) = (l ++ [x]) ++ E :: (c ++ l') := by
      show swapAt (l ++ E :: x :: (c ++ l')) l.length = _
      rw [swapAt_mid]
      simp
    rw [e, show l.length + 1 = (l ++ [x]).length by simp, real_bubbleR E l' c (l ++ [x])]
    simp

/-- Moving a box to the left past a block. -/
theorem real_bubbleL (F : Box) (c : List Box) : ∀ (l l' : List Box),
    real (l ++ c ++ F :: l') (swaps l.length (List.range c.length).reverse) = l ++ F :: (c ++ l') := by
  induction c using List.reverseRecOn with
  | nil => intro l l'; simp [swaps]
  | append_singleton c x ih =>
    intro l l'
    have e : Move.app (l ++ (c ++ [x]) ++ F :: l') (.swap (l.length + c.length)) =
        l ++ c ++ F :: x :: l' := by
      show swapAt (l ++ (c ++ [x]) ++ F :: l') (l.length + c.length) = _
      have h := swapAt_mid (l ++ c) l' x F
      rw [List.length_append] at h
      rw [show l ++ (c ++ [x]) ++ F :: l' = l ++ c ++ x :: F :: l' by simp, h]
    rw [List.length_append, List.length_singleton, swaps_range_succ_reverse, real_cons, e,
      ih l (x :: l')]
    simp

/-! ### Naturality of a swap and a split of one of the swapped boxes -/

theorem splitAt_mid (l l' : List Box) (E : Box) (p : ℕ) :
    splitAt (l ++ E :: l') l.length p = l ++ kids E p ++ l' := by
  have h := splitAt_append_right l (E :: l') 0 p
  rw [add_zero] at h
  rw [h]
  simp [splitAt]

theorem splitAt_mid_succ (l l' : List Box) (E F : Box) (p : ℕ) :
    splitAt (l ++ E :: F :: l') (l.length + 1) p = l ++ E :: (kids F p ++ l') := by
  rw [splitAt_append_right l (E :: F :: l') 1 p]
  simp [splitAt]

/-- (d): a swap followed by a split of the first box is a split of the second box followed by
moving the old first box past the new block. -/
theorem splitAt_swapAt_self (l l' : List Box) (E F : Box) (p : ℕ) :
    splitAt (swapAt (l ++ E :: F :: l') l.length) l.length p =
      real (splitAt (l ++ E :: F :: l') (l.length + 1) p) (swaps l.length (List.range p)) := by
  have h := real_bubbleR E l' (kids F p) l
  rw [length_kids] at h
  rw [swapAt_mid, splitAt_mid, splitAt_mid_succ, h]

/-- (d): a swap followed by a split of the second box is a split of the first box followed by
moving the old second box back past the new block. -/
theorem splitAt_swapAt_succ (l l' : List Box) (E F : Box) (p : ℕ) :
    splitAt (swapAt (l ++ E :: F :: l') l.length) (l.length + 1) p =
      real (splitAt (l ++ E :: F :: l') l.length p) (swaps l.length (List.range p).reverse) := by
  have h := real_bubbleL F (kids E p) l l'
  rw [length_kids] at h
  rw [swapAt_mid, splitAt_mid_succ, splitAt_mid, h]

/-! ### Layers -/

theorem layer_succ (i n q : ℕ) : layer i (n + 1) q = .split i q :: layer (i + q) n q := by
  simp only [layer, List.range_succ_eq_map, List.map_cons, List.map_map, zero_mul, add_zero]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply]
  congr 1
  rw [Nat.succ_mul]
  omega

/-- A layer splits each box of a block by `q`, left to right. -/
theorem real_layer (q : ℕ) (l' : List Box) : ∀ (c l : List Box),
    real (l ++ c ++ l') (layer l.length c.length q) = l ++ c.flatMap (fun E => kids E q) ++ l'
  | [], l => by simp [layer]
  | x :: c, l => by
    rw [List.length_cons, layer_succ, real_cons]
    have e : Move.app (l ++ x :: c ++ l') (.split l.length q) = (l ++ kids x q) ++ c ++ l' := by
      show splitAt (l ++ x :: c ++ l') l.length q = _
      rw [show l ++ x :: c ++ l' = l ++ x :: (c ++ l') by simp, splitAt_mid]
      simp
    rw [e, show l.length + q = (l ++ kids x q).length by simp, real_layer q l' c (l ++ kids x q)]
    simp

end GroupApproximation.ClassTransposition.Presentation
