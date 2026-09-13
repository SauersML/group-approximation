import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Nat.Find
import GroupApproximation.Meta.AxiomGuard

/-!
# List lemmas for the polygons of Lemma 9.4

The list combinatorics behind `OsinLemma94PolygonPartitionInput`: the walk of a face is split
into runs, short runs are cut into chunks, and a run along a closed chain is a cyclic arc.

* `chunks`: greedy chunks of a fixed length, with `flatten_chunks`, `nil_notMem_chunks`,
  `length_le_of_mem_chunks` and `isChain_chunks` (every chunk before the last is full).
* `head?_flatten_of_mem_head?`, `getLast?_flatten_of_mem_getLast?`: the ends of a flattening.
* `range_flatMap_getD`: reading a list of lists by index.
* `head?_flatten_ne_of_lt`: in a duplicate-free flattening, no later list starts the flattening.
* `getElem_of_isChain_closed`, `exists_cyclicArc_of_isChain`, `idxOf_eq_succ_or_zero`: a chain
  of a functional relation along a closed duplicate-free chain is a cyclic arc of it.
* `exists_cyclicArc_of_isChain_idxOf`: a list whose positions increase by one is an arc.
* `sectionIndex`: the section of a position between cuts.
-/

namespace GroupApproximation.GGT.VanKampen

universe v

namespace PolygonList

variable {α : Type*}

/-! ## Chunks -/

/-- Greedy chunks of length `n`; the last chunk may be shorter.  For `n = 0` the chunks are
single entries. -/
def chunks (n : ℕ) : List α → List (List α)
  | [] => []
  | a :: l => (a :: l.take (n - 1)) :: chunks n (l.drop (n - 1))
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

@[simp] theorem chunks_nil (n : ℕ) : chunks n ([] : List α) = [] := by
  simp only [chunks]

theorem chunks_cons (n : ℕ) (a : α) (l : List α) :
    chunks n (a :: l) = (a :: l.take (n - 1)) :: chunks n (l.drop (n - 1)) := by
  simp only [chunks]

/-- The chunks read the list. -/
theorem flatten_chunks (n : ℕ) : ∀ l : List α, (chunks n l).flatten = l
  | [] => by rw [chunks_nil, List.flatten_nil]
  | a :: l => by
    rw [chunks_cons, List.flatten_cons, flatten_chunks n (l.drop (n - 1)), List.cons_append,
      List.take_append_drop]
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- No chunk is empty. -/
theorem nil_notMem_chunks (n : ℕ) : ∀ l : List α, [] ∉ chunks n l
  | [] => by simp
  | a :: l => by
    rw [chunks_cons, List.mem_cons, not_or]
    exact ⟨(List.cons_ne_nil _ _).symm, nil_notMem_chunks n (l.drop (n - 1))⟩
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- Every chunk has length at most `n`. -/
theorem length_le_of_mem_chunks {n : ℕ} (hn : 1 ≤ n) :
    ∀ l : List α, ∀ m ∈ chunks n l, m.length ≤ n
  | [] => by simp
  | a :: l => by
    intro m hm
    rw [chunks_cons, List.mem_cons] at hm
    rcases hm with rfl | hm
    · rw [List.length_cons, List.length_take]
      omega
    · exact length_le_of_mem_chunks hn (l.drop (n - 1)) m hm
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- Every chunk followed by another chunk is full. -/
theorem isChain_chunks {n : ℕ} (hn : 1 ≤ n) :
    ∀ l : List α, (chunks n l).IsChain fun m m' => m.length = n ∧ m' ≠ []
  | [] => by rw [chunks_nil]; exact List.IsChain.nil
  | a :: l => by
    rw [chunks_cons]
    have ih := isChain_chunks hn (l.drop (n - 1))
    rcases hl : l.drop (n - 1) with _ | ⟨b, l'⟩
    · rw [chunks_nil]
      exact List.isChain_singleton _
    · rw [hl] at ih
      refine List.isChain_cons.mpr ⟨fun y hy => ?_, ih⟩
      rw [chunks_cons, List.head?_cons] at hy
      have hy' : b :: l'.take (n - 1) = y := Option.some_inj.mp hy
      rw [← hy']
      refine ⟨?_, List.cons_ne_nil _ _⟩
      have h := congrArg List.length hl
      rw [List.length_drop, List.length_cons] at h
      rw [List.length_cons, List.length_take]
      omega
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- A chunk is an infix of the list. -/
theorem infix_of_mem_chunks {n : ℕ} {l m : List α} (hm : m ∈ chunks n l) : m <:+: l := by
  have h := List.infix_of_mem_flatten hm
  rwa [flatten_chunks] at h

/-! ## Ends of a flattening -/

/-- The first list of a flattening of nonempty lists starts the flattening. -/
theorem head?_flatten_of_mem_head? :
    ∀ {L : List (List α)} {x : List α}, [] ∉ L → x ∈ L.head? → x.head? = L.flatten.head?
  | [], _, _, hx => by simp at hx
  | y :: L, x, hL, hx => by
    rw [List.head?_cons] at hx
    have hx' : y = x := Option.some_inj.mp hx
    have hy : y ≠ [] := by
      rintro rfl
      exact hL (List.mem_cons_self ..)
    rw [← hx', List.flatten_cons, List.head?_append_of_ne_nil _ hy]

/-- The last list of a flattening of nonempty lists ends the flattening. -/
theorem getLast?_flatten_of_mem_getLast? :
    ∀ {L : List (List α)} {x : List α}, [] ∉ L → x ∈ L.getLast? → x.getLast? = L.flatten.getLast?
  | [], _, _, hx => by simp at hx
  | [y], x, _, hx => by
    rw [List.getLast?_singleton] at hx
    have hx' : y = x := Option.some_inj.mp hx
    rw [← hx', List.flatten_cons, List.flatten_nil, List.append_nil]
  | y :: z :: L, x, hL, hx => by
    have hL' : [] ∉ z :: L := fun h => hL (List.mem_cons_of_mem _ h)
    rw [List.getLast?_cons_cons] at hx
    have hxmem : x ∈ z :: L := List.mem_of_mem_getLast? hx
    have hxne : x ≠ [] := by
      rintro rfl
      exact hL' hxmem
    rw [List.flatten_cons, List.getLast?_append, ← getLast?_flatten_of_mem_getLast? hL' hx]
    cases hxl : x.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hxl) hxne
    | some b => rfl

/-! ## Reading by index -/

theorem map_getD_range (l : List (List α)) :
    (List.range l.length).map (fun i => l.getD i []) = l := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem _ _ h₂

/-- Reading a list of lists by index. -/
theorem range_flatMap_getD {β : Type*} (l : List (List α)) (g : List α → List β) :
    (List.range l.length).flatMap (fun i => g (l.getD i [])) = l.flatMap g := by
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  conv_rhs => rw [← map_getD_range l]
  rw [List.map_map]
  rfl

/-- In a duplicate-free flattening of nonempty lists, no later list starts the flattening. -/
theorem head?_flatten_ne_of_lt {L : List (List α)} (hL : [] ∉ L) (hnodup : L.flatten.Nodup)
    {i : ℕ} (hi : i + 1 < L.length) {e : α} (he : e ∈ L[i + 1].head?) :
    L.flatten.head? ≠ some e := by
  intro hhead
  have hsplit : L.flatten =
      (L.take (i + 1)).flatten ++ (L[i + 1] ++ (L.drop (i + 1 + 1)).flatten) := by
    conv_lhs => rw [← List.take_append_drop (i + 1) L, List.drop_eq_getElem_cons hi]
    rw [List.flatten_append, List.flatten_cons]
  have htake : (L.take (i + 1)).flatten ≠ [] := by
    intro h
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil (L.take (i + 1))
      (List.ne_nil_of_length_pos (by rw [List.length_take]; omega))
    have hm0 : m = [] := List.flatten_eq_nil_iff.mp h m hm
    rw [hm0] at hm
    exact hL (List.mem_of_mem_take hm)
  rw [hsplit] at hnodup hhead
  rw [List.head?_append_of_ne_nil _ htake] at hhead
  exact (List.nodup_append.mp hnodup).2.2 e (List.mem_of_mem_head? hhead) e
    (List.mem_append_left _ (List.mem_of_mem_head? he)) rfl

/-! ## Arcs of a closed chain -/

/-- A closed chain relates each entry to the next one, cyclically. -/
theorem rel_getElem_mod {r : α → α → Prop} {O : List α} (hne : O ≠ []) (hchain : O.IsChain r)
    (hclose : r (O.getLast hne) (O.head hne)) (m : ℕ) (hm : m < O.length) :
    r O[m] (O[(m + 1) % O.length]'(Nat.mod_lt _ (by omega))) := by
  by_cases h : m + 1 < O.length
  · simp only [Nat.mod_eq_of_lt h]
    exact List.isChain_iff_getElem.mp hchain m h
  · have hlast : m = O.length - 1 := by omega
    have e : (m + 1) % O.length = 0 := by
      rw [show m + 1 = O.length by omega, Nat.mod_self]
    simp only [e, List.getElem_zero]
    simp only [List.getLast_eq_getElem] at hclose
    subst hlast
    exact hclose

/-- A chain of a functional relation, starting at entry `s` of a closed chain, follows it. -/
theorem getElem_of_isChain_closed {r : α → α → Prop} {O : List α} (hne : O ≠ [])
    (hchain : O.IsChain r) (hclose : r (O.getLast hne) (O.head hne))
    (hfun : ∀ a b b', r a b → r a b' → b = b') {t : List α} (ht : t.IsChain r) {s : ℕ}
    (hs : s < O.length) (hhead : t.head? = some O[s]) :
    ∀ (k : ℕ) (hk : k < t.length), t[k] = O[(s + k) % O.length]'(Nat.mod_lt _ (by omega))
  | 0, hk => by
    simp only [Nat.add_zero, Nat.mod_eq_of_lt hs]
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk] at hhead
    exact Option.some_inj.mp hhead
  | k + 1, hk => by
    have ih := getElem_of_isChain_closed hne hchain hclose hfun ht hs hhead k (by omega)
    have hstep := rel_getElem_mod hne hchain hclose ((s + k) % O.length)
      (Nat.mod_lt _ (by omega))
    have hk' := List.isChain_iff_getElem.mp ht k hk
    rw [ih] at hk'
    rw [hfun _ _ _ hk' hstep]
    simp only [Nat.mod_add_mod, Nat.add_assoc]

/-- A duplicate-free chain of a functional relation inside a closed duplicate-free chain is a
cyclic arc of it. -/
theorem exists_cyclicArc_of_isChain {r : α → α → Prop} {O : List α} (hne : O ≠ [])
    (hchain : O.IsChain r) (hclose : r (O.getLast hne) (O.head hne))
    (hfun : ∀ a b b', r a b → r a b' → b = b') {t : List α} (ht : t.IsChain r)
    (htnodup : t.Nodup) (hsub : t ⊆ O) : ∃ arc : Embedded.CyclicArc O, arc.darts = t := by
  rcases t with _ | ⟨x, t'⟩
  · exact ⟨⟨0, 0, Nat.zero_le _⟩, by simp [Embedded.CyclicArc.darts]⟩
  · have hx : x ∈ O := hsub (List.mem_cons_self ..)
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
    have hlen : (O[s] :: t').length ≤ O.length := (List.subperm_of_subset htnodup hsub).length_le
    refine ⟨⟨⟨s, by omega⟩, (O[s] :: t').length, hlen⟩, ?_⟩
    apply List.ext_getElem
    · exact Embedded.CyclicArc.darts_length _
    · intro k h₁ h₂
      rw [getElem_of_isChain_closed hne hchain hclose hfun ht hs rfl k h₂]
      simp only [Embedded.CyclicArc.darts, Embedded.CyclicArc.rotated_eq_rotate,
        List.getElem_take, List.getElem_rotate, Nat.add_comm k s]

theorem idxOf_getElem_of_nodup [BEq α] [LawfulBEq α] {O : List α} (hnodup : O.Nodup) (i : ℕ)
    (hi : i < O.length) : O.idxOf O[i] = i :=
  List.get_idxOf hnodup ⟨i, hi⟩

/-- Along a closed duplicate-free chain of a functional relation, the next entry is at the next
position, or at position `0`. -/
theorem idxOf_eq_succ_or_zero [BEq α] [LawfulBEq α] {r : α → α → Prop} {O : List α}
    (hne : O ≠ []) (hnodup : O.Nodup) (hchain : O.IsChain r)
    (hclose : r (O.getLast hne) (O.head hne)) (hfun : ∀ a b b', r a b → r a b' → b = b')
    {e e' : α} (he : e ∈ O) (hr : r e e') :
    O.idxOf e' = O.idxOf e + 1 ∨ O.idxOf e' = 0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  rw [hfun _ _ _ hr (rel_getElem_mod hne hchain hclose i hi), idxOf_getElem_of_nodup hnodup,
    idxOf_getElem_of_nodup hnodup]
  by_cases h : i + 1 < O.length
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · exact Or.inr (by rw [show i + 1 = O.length by omega, Nat.mod_self])

/-- A list whose positions in a duplicate-free list increase by one is an arc of it. -/
theorem exists_cyclicArc_of_isChain_idxOf [BEq α] [LawfulBEq α] {O t : List α}
    (hnodup : O.Nodup) (hsub : ∀ d ∈ t, d ∈ O)
    (hchain : t.IsChain fun d d' => O.idxOf d' = O.idxOf d + 1) :
    ∃ arc : Embedded.CyclicArc O, arc.darts = t ∧
      ∀ (k : ℕ) (hk : k < t.length), O.idxOf t[k] = arc.start.1 + k := by
  rcases t with _ | ⟨x, t'⟩
  · exact ⟨⟨0, 0, Nat.zero_le _⟩, by simp [Embedded.CyclicArc.darts],
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  · have hpos : ∀ (k : ℕ) (hk : k < (x :: t').length),
        O.idxOf (x :: t')[k] = O.idxOf x + k := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [List.isChain_iff_getElem.mp hchain k hk, ih (by omega)]
        omega
    have hx : x ∈ O := hsub x (List.mem_cons_self ..)
    have hs : O.idxOf x < O.length := List.idxOf_lt_length_iff.mpr hx
    have hlast := hpos t'.length (by simp)
    have hbound : O.idxOf (x :: t')[t'.length] < O.length :=
      List.idxOf_lt_length_iff.mpr (hsub _ (List.getElem_mem _))
    refine ⟨⟨⟨O.idxOf x, by omega⟩, (x :: t').length, by simp only [List.length_cons]; omega⟩,
      ?_, fun k hk => hpos k hk⟩
    apply List.ext_getElem
    · exact Embedded.CyclicArc.darts_length _
    · intro k h₁ h₂
      have hk := hpos k h₂
      obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem (hsub _ (List.getElem_mem h₂))
      rw [← hieq, idxOf_getElem_of_nodup hnodup] at hk
      have hmod : (k + O.idxOf x) % O.length = i := by
        rw [hk, Nat.add_comm, Nat.mod_eq_of_lt (by omega)]
      simp only [Embedded.CyclicArc.darts, Embedded.CyclicArc.rotated_eq_rotate,
        List.getElem_take, List.getElem_rotate, hmod]
      exact hieq

/-! ## Sections between cuts -/

/-- A cut position, extended by `0` past the last cut. -/
def cutAt {count : ℕ} (cut : Fin (count + 1) → ℕ) (j : ℕ) : ℕ :=
  if h : j < count + 1 then cut ⟨j, h⟩ else 0

theorem cutAt_of_lt {count : ℕ} (cut : Fin (count + 1) → ℕ) {j : ℕ} (h : j < count + 1) :
    cutAt cut j = cut ⟨j, h⟩ :=
  dif_pos h

/-- The section of a position: the last of the first `count` cuts at or before it. -/
def sectionIndex {count : ℕ} (cut : Fin (count + 1) → ℕ) (p : ℕ) : ℕ :=
  Nat.findGreatest (fun j => cutAt cut j ≤ p) (count - 1)

theorem sectionIndex_lt {count : ℕ} (hcount : 0 < count) (cut : Fin (count + 1) → ℕ) (p : ℕ) :
    sectionIndex cut p < count := by
  have h := Nat.findGreatest_le (P := fun j => cutAt cut j ≤ p) (count - 1)
  unfold sectionIndex
  omega

theorem cutAt_sectionIndex_le {count : ℕ} (cut : Fin (count + 1) → ℕ)
    (hzero : cutAt cut 0 = 0) (p : ℕ) : cutAt cut (sectionIndex cut p) ≤ p :=
  Nat.findGreatest_spec (P := fun j => cutAt cut j ≤ p) (Nat.zero_le _)
    (by show cutAt cut 0 ≤ p; rw [hzero]; exact Nat.zero_le p)

theorem lt_cutAt_sectionIndex_succ {count : ℕ} (hcount : 0 < count)
    (cut : Fin (count + 1) → ℕ) {p : ℕ} (hp : p < cutAt cut count) :
    p < cutAt cut (sectionIndex cut p + 1) := by
  by_cases h : sectionIndex cut p + 1 ≤ count - 1
  · exact not_le.mp (Nat.findGreatest_is_greatest (P := fun j => cutAt cut j ≤ p)
      (k := sectionIndex cut p + 1) (by unfold sectionIndex; omega) h)
  · have hle := Nat.findGreatest_le (P := fun j => cutAt cut j ≤ p) (count - 1)
    have heq : sectionIndex cut p + 1 = count := by
      unfold sectionIndex at h ⊢
      omega
    rw [heq]
    exact hp

end PolygonList

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PolygonList.isChain_chunks
#audit_axioms GroupApproximation.GGT.VanKampen.PolygonList.getLast?_flatten_of_mem_getLast?
#audit_axioms GroupApproximation.GGT.VanKampen.PolygonList.range_flatMap_getD
#audit_axioms GroupApproximation.GGT.VanKampen.PolygonList.head?_flatten_ne_of_lt
#audit_axioms GroupApproximation.GGT.VanKampen.PolygonList.exists_cyclicArc_of_isChain
#audit_axioms GroupApproximation.GGT.VanKampen.PolygonList.idxOf_eq_succ_or_zero
#audit_axioms GroupApproximation.GGT.VanKampen.PolygonList.exists_cyclicArc_of_isChain_idxOf
#audit_axioms GroupApproximation.GGT.VanKampen.PolygonList.lt_cutAt_sectionIndex_succ
