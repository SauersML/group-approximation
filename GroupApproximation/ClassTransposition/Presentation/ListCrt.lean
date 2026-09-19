import GroupApproximation.ClassTransposition.Presentation.ListBlock
import GroupApproximation.ClassTransposition.Presentation.Perms

/-!
# The colour exchange on lists of boxes

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §2,
relation (c)).

Splitting a box by `q` and then its children by `p` gives the same `pq` boxes as splitting by `p`
and then by `q` (CRT). The two lists differ by a permutation, so some swap word turns one into the
other (`crt_spec`). The word chosen by `crtWord` works at every box of every list (`real_cx`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

theorem real_swaps_zero : ∀ (b : List Box) (w : List ℕ), real b (swaps 0 w) = swapList b w
  | _, [] => rfl
  | b, k :: w => by
    show real (swapAt b (0 + k)) (swaps 0 w) = swapList (swapAt b k) w
    rw [zero_add, real_swaps_zero]

/-- Swaps inside a block act on the block. -/
theorem real_swaps_mid (l l' : List Box) : ∀ (c : List Box) (w : List ℕ),
    (∀ k ∈ w, k + 1 < c.length) → real (l ++ c ++ l') (swaps l.length w) = l ++ swapList c w ++ l'
  | _, [], _ => rfl
  | c, k :: w, hw => by
    have hk := hw k List.mem_cons_self
    have e : swapAt (l ++ c ++ l') (l.length + k) = l ++ swapAt c k ++ l' := by
      rw [List.append_assoc, swapAt_append_right, swapAt_append_left c l' k hk, List.append_assoc]
    show real (swapAt (l ++ c ++ l') (l.length + k)) (swaps l.length w) =
      l ++ swapList (swapAt c k) w ++ l'
    rw [e]
    exact real_swaps_mid l l' (swapAt c k) w fun k' hk' => by
      rw [length_swapAt]; exact hw k' (List.mem_cons_of_mem _ hk')

theorem swapAt_map {α β : Type*} (f : α → β) : ∀ (l : List α) (k : ℕ),
    swapAt (l.map f) k = (swapAt l k).map f
  | [], _ => rfl
  | [_], 0 => rfl
  | _ :: _ :: _, 0 => rfl
  | a :: l, k + 1 => by
    rw [List.map_cons, swapAt_succ, swapAt_succ, List.map_cons, swapAt_map f l k]

theorem swapList_map {α β : Type*} (f : α → β) : ∀ (l : List α) (w : List ℕ),
    swapList (l.map f) w = (swapList l w).map f
  | _, [] => rfl
  | l, k :: w => by
    show swapList (swapAt (l.map f) k) w = (swapList (swapAt l k) w).map f
    rw [swapAt_map, swapList_map]

theorem kids_place (E X : Box) (p : ℕ) : kids (place E X) p = (kids X p).map (place E) := by
  simp only [kids, List.map_map]
  exact List.map_congr_left fun j _ => (place_assoc E X (child p j)).symm

theorem kids_eq_map (E : Box) (p : ℕ) : kids E p = (kids univ p).map (place E) := by
  rw [← kids_place, place_univ]

theorem nodup_of_disj {l : List Box} (h : l.Pairwise Box.Disj) : l.Nodup :=
  h.imp fun {X Y} hXY heq => by
    subst heq
    have := X.elt_mem 0
    exact hXY _ this this

theorem swapList_append {α : Type*} : ∀ (l : List α) (u v : List ℕ),
    swapList l (u ++ v) = swapList (swapList l u) v
  | _, [], _ => rfl
  | l, k :: u, v => swapList_append (swapAt l k) u v

theorem swapList_cons_succ {α : Type*} (y : α) : ∀ (t : List α) (w : List ℕ),
    swapList (y :: t) (w.map (· + 1)) = y :: swapList t w
  | _, [] => rfl
  | t, k :: w => by
    show swapList (swapAt (y :: t) (k + 1)) (w.map (· + 1)) = y :: swapList (swapAt t k) w
    rw [swapAt_succ, swapList_cons_succ]

/-- Moving an element to the front. -/
theorem swapList_front {α : Type*} (y : α) (pre : List α) : ∀ post : List α,
    swapList (pre ++ y :: post) (List.range pre.length).reverse = y :: (pre ++ post) := by
  induction pre using List.reverseRecOn with
  | nil => intro post; rfl
  | append_singleton pre x ih =>
    intro post
    rw [List.length_append, List.length_singleton, List.range_succ, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    show swapList (swapAt (pre ++ [x] ++ y :: post) pre.length) _ = _
    have h := swapAt_append_right pre (x :: y :: post) 0
    rw [add_zero, swapAt_zero] at h
    rw [List.append_assoc, List.singleton_append, h, ih (x :: post)]
    simp

/-- A swap word sorts a list of distinct elements into any permutation of it. -/
theorem exists_swapList {α : Type*} : ∀ (l l' : List α), l.Nodup → l.Perm l' →
    ∃ w : List ℕ, (∀ k ∈ w, k + 1 < l.length) ∧ swapList l w = l'
  | l, [], _, hp => ⟨[], by simp, by rw [hp.eq_nil]; rfl⟩
  | l, y :: r, hn, hp => by
    have hy : y ∈ l := hp.symm.subset List.mem_cons_self
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hy
    have hp' : (pre ++ post).Perm r := (List.perm_middle.symm.trans hp).cons_inv
    have hn' : (pre ++ post).Nodup := (List.perm_middle.nodup_iff.1 hn).of_cons
    obtain ⟨w, hw, hsw⟩ := exists_swapList (pre ++ post) r hn' hp'
    refine ⟨(List.range pre.length).reverse ++ w.map (· + 1), ?_, ?_⟩
    · intro k hk
      rcases List.mem_append.1 hk with hk | hk
      · rw [List.mem_reverse, List.mem_range] at hk
        simp only [List.length_append, List.length_cons]
        omega
      · obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
        have := hw k' hk'
        simp only [List.length_append, List.length_cons] at this ⊢
        omega
    · rw [swapList_append, swapList_front, swapList_cons_succ, hsw]

/-! ### The two orders of the `pq` grandchildren -/

theorem real_split_layer (E : Box) (p q : ℕ) (l l' : List Box) :
    real (l ++ E :: l') (.split l.length p :: layer l.length p q) =
      l ++ (kids E p).flatMap (fun Y => kids Y q) ++ l' := by
  rw [real_cons]
  show real (splitAt (l ++ E :: l') l.length p) _ = _
  rw [splitAt_mid]
  have h := real_layer q l' (kids E p) l
  rwa [length_kids] at h

theorem mem_kk {p q : ℕ} (hq : 0 < q) (X : Box) :
    X ∈ (kids univ q).flatMap (fun Y => kids Y p) ↔ X.m = (p : ℤ) * q := by
  constructor
  · intro h
    obtain ⟨Y, hY, hX⟩ := List.mem_flatMap.1 h
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hY
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hX
    simp [place, child, univ]
  · intro hm
    have h1 := X.hr
    have h2 := X.hrm
    have hq' : (0 : ℤ) < q := by exact_mod_cast hq
    have hu0 := Int.emod_nonneg X.r hq'.ne'
    have hu1 := Int.emod_lt_of_pos X.r hq'
    have ht0 : 0 ≤ X.r / q := Int.ediv_nonneg h1 hq'.le
    have ht1 : X.r / q < p := by
      rw [Int.ediv_lt_iff_lt_mul hq']; rw [hm] at h2; linarith
    refine List.mem_flatMap.2 ⟨place univ (child q ⟨(X.r % q).toNat, by omega⟩), List.mem_map.2
      ⟨_, List.mem_finRange _, rfl⟩, List.mem_map.2 ⟨⟨(X.r / q).toNat, by omega⟩, List.mem_finRange _,
      ?_⟩⟩
    ext
    · simp only [place, child, univ, Int.toNat_of_nonneg hu0, Int.toNat_of_nonneg ht0]
      have := Int.emod_add_ediv X.r q
      linarith
    · simp only [place, child, univ, hm]
      ring

theorem real_univ_layer (p q : ℕ) :
    real [univ] (.split 0 q :: layer 0 q p) = (kids univ q).flatMap (fun Y => kids Y p) := by
  simpa using real_split_layer univ q p [] []

theorem length_kk {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ((kids univ q).flatMap (fun Y => kids Y p)).length = p * q := by
  rw [← real_univ_layer, length_real, levW_cons]
  show levW ((Move.split 0 q).lev 1) (layer 0 q p) = p * q
  rw [lev_split q (by norm_num), levW_layer hp q 0 _ (by omega), show 1 + q - 1 = q by omega,
    add_comm, mul_pred_add hp]

theorem crt_exists {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∃ w : List ℕ, (∀ k ∈ w, k + 1 < p * q) ∧
      real [univ] (.split 0 q :: layer 0 q p ++ swaps 0 w) = real [univ] (.split 0 p :: layer 0 p q) := by
  have hA : ((kids univ q).flatMap (fun Y => kids Y p)).Nodup := by
    rw [← real_univ_layer]
    refine nodup_of_disj (isPart_real isPart_univ _ ?_).1
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hq
    · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hm; exact hp
  have hAB : ((kids univ q).flatMap (fun Y => kids Y p)).Perm
      ((kids univ p).flatMap (fun Y => kids Y q)) := by
    refine (List.perm_ext_iff_of_nodup hA ?_).2 fun X => by rw [mem_kk hq, mem_kk hp, mul_comm]
    rw [← real_univ_layer]
    refine nodup_of_disj (isPart_real isPart_univ _ ?_).1
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hp
    · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hm; exact hq
  obtain ⟨w, hw, hsw⟩ := exists_swapList _ _ hA hAB
  refine ⟨w, fun k hk => ?_, ?_⟩
  · have := hw k hk
    rwa [length_kk hp hq] at this
  · rw [real_append, real_univ_layer, real_swaps_zero, hsw, real_univ_layer]

theorem crt_spec {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (∀ k ∈ crtWord p q, k + 1 < p * q) ∧
      real [univ] (.split 0 q :: layer 0 q p ++ swaps 0 (crtWord p q)) =
        real [univ] (.split 0 p :: layer 0 p q) := by
  unfold crtWord
  rw [dif_pos (crt_exists hp hq)]
  exact Classical.choose_spec (crt_exists hp hq)

theorem kk_place (E : Box) (p q : ℕ) :
    (kids E q).flatMap (fun Y => kids Y p) =
      ((kids univ q).flatMap (fun Y => kids Y p)).map (place E) := by
  rw [kids_eq_map E q, List.flatMap_map, List.map_flatMap]
  exact List.flatMap_congr fun Y _ => kids_place E Y p

/-- (c) on lists: the colour exchange holds at every box. -/
theorem real_cx {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (E : Box) (l l' : List Box) :
    real (l ++ E :: l') (.split l.length p :: layer l.length p q) =
      real (l ++ E :: l') (.split l.length q :: layer l.length q p ++ swaps l.length (crtWord p q)) := by
  obtain ⟨hw, hs⟩ := crt_spec hp hq
  rw [real_append, real_univ_layer, real_swaps_zero, real_univ_layer] at hs
  rw [real_split_layer, real_append, real_split_layer, real_swaps_mid, kk_place E p q,
    kk_place E q p, swapList_map, hs]
  intro k hk
  rw [kk_place, List.length_map, length_kk hp hq]
  exact hw k hk

end GroupApproximation.ClassTransposition.Presentation
