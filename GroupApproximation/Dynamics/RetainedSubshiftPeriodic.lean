import GroupApproximation.Dynamics.RetainedSubshift
import GroupApproximation.Dynamics.SubshiftCyclePeriodic
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Periodic points of the retained subshifts

`non_mf_groups_exist.tex`, proof of `lem:chain-core-models` (tex 1402–1406):

> Retain only the cyclic edges at level `r`, and let `Z_r` be the subshift read from bi-infinite
> paths in this graph.  Every finite path in the retained graph lies in a strongly connected
> component and extends to a periodic path.  Thus `Z_r` has dense periodic points and satisfies
> the cycle condition.  It is nonempty, ...

* `isCyclicEdge_window_of_periodic`: the windows of a periodic word whose windows are words of `X`
  are cyclic edges of `X`, because the periodic orbit is a closed walk through each of them;
* `exists_periodic_extension`, `exists_periodic_agree_retainedSubshift`: a finite piece of a point of
  `Z_r` extends to a periodic point of `Z_r` (the path returns through its cyclic edges);
* `cycleCondition_retainedSubshift`: `Z_r` satisfies the cycle condition;
* `retainedSubshift_nonempty`: `Z_r` is nonempty for a nonempty subshift over a finite alphabet
  (two equal words along a point of `X` close a cycle).
-/

namespace GroupApproximation

namespace WordGraph

open SymbolicDynamics.FullShift

variable {A : Type*}

/-- Consecutive words of a point of `X` are joined by a directed path of the word graph. -/
theorem reflTransGen_word {X : Set (ℤ → A)} (hX : ∀ n : ℤ, Set.MapsTo (shift n) X X)
    {x : ℤ → A} (hx : x ∈ X) (i : ℤ) (r n : ℕ) :
    Relation.ReflTransGen (wordEdge X r) (word x i r) (word x (i + n) r) := by
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero, Relation.ReflTransGen.refl]
  | succ n ih =>
    rw [show i + ((n + 1 : ℕ) : ℤ) = i + n + 1 by omega]
    exact ih.tail (wordEdge_word hX hx (i + n) r)

/-- The windows of a periodic word all of whose windows are words of `X` are cyclic edges of `X`:
the periodic orbit is a closed walk through each of them. -/
theorem isCyclicEdge_window_of_periodic {X : Set (ℤ → A)} {r k : ℕ} [NeZero k] (p : ZMod k → A)
    (hp : ∀ n : ZMod k, (fun j : Fin (r + 1) => p (n + (j : ℕ))) ∈ language X (r + 1))
    (n : ZMod k) : IsCyclicEdge X r (fun j : Fin (r + 1) => p (n + (j : ℕ))) := by
  refine ⟨hp n, ?_⟩
  let vtx : ℕ → Fin r → A := fun i j => p (n + (i : ℕ) + (j : ℕ))
  have hstep : ∀ i : ℕ, wordEdge X r (vtx i) (vtx (i + 1)) := fun i =>
    ⟨fun j : Fin (r + 1) => p (n + (i : ℕ) + (j : ℕ)), hp (n + (i : ℕ)), funext fun _ => rfl,
      funext fun j => congrArg p (by simp only [Fin.val_succ]; push_cast; ring)⟩
  have hwalk : ∀ i : ℕ, Relation.ReflTransGen (wordEdge X r) (vtx 1) (vtx (1 + i)) := by
    intro i
    induction i with
    | zero => simp only [add_zero, Relation.ReflTransGen.refl]
    | succ i ih =>
      refine ih.tail ?_
      rw [show 1 + (i + 1) = 1 + i + 1 by omega]
      exact hstep (1 + i)
  have htail : Fin.tail (fun j : Fin (r + 1) => p (n + (j : ℕ))) = vtx 1 :=
    funext fun j => congrArg p (by simp only [Fin.val_succ]; push_cast; ring)
  have hinit : Fin.init (fun j : Fin (r + 1) => p (n + (j : ℕ))) = vtx k :=
    funext fun j => congrArg p (by rw [ZMod.natCast_self, add_zero, Fin.val_castSucc])
  have hk : 1 + (k - 1) = k := by have := NeZero.pos k; omega
  have h := hwalk (k - 1)
  rw [hk] at h
  rw [htail, hinit]
  exact h

end WordGraph

namespace ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

variable {A : Type*}

theorem isCyclicEdge_word_of_mem_retainedSubshift {X : Set (ℤ → A)} {r : ℕ} {z : ℤ → A}
    (hz : z ∈ retainedSubshift X r) (i : ℤ) : IsCyclicEdge X r (word z i (r + 1)) := by
  rw [retainedSubshift_eq_iInter] at hz
  exact Set.mem_iInter.1 hz i

theorem mem_retainedSubshift_of_forall {X : Set (ℤ → A)} {r : ℕ} {z : ℤ → A}
    (h : ∀ i : ℤ, IsCyclicEdge X r (word z i (r + 1))) : z ∈ retainedSubshift X r := by
  rw [retainedSubshift_eq_iInter]
  exact Set.mem_iInter.2 h

/-- Along a point of `Z_r`, every edge is cyclic, so the path from position `0` to `m` returns. -/
theorem reflTransGen_word_zero_of_mem_retainedSubshift {X : Set (ℤ → A)} {r : ℕ} {z : ℤ → A}
    (hz : z ∈ retainedSubshift X r) (m : ℕ) :
    Relation.ReflTransGen (wordEdge X r) (word z m r) (word z 0 r) := by
  induction m with
  | zero => simp only [Nat.cast_zero, Relation.ReflTransGen.refl]
  | succ m ih =>
    have h := (isCyclicEdge_word_of_mem_retainedSubshift hz m).2
    rw [tail_word, init_word] at h
    rw [Nat.cast_succ]
    exact h.trans ih

/-- **Periodic extension** (tex 1403–1405): the path of `z ∈ Z_r` through the positions `0, …, m`
returns through its cyclic edges, and reading this closed walk gives a periodic word whose windows
are words of `X` and whose first letters are `z 0, …, z m`. -/
theorem exists_periodic_extension {X : Set (ℤ → A)} {r : ℕ} {z : ℤ → A}
    (hz : z ∈ retainedSubshift X r) (m : ℕ) :
    ∃ (k : ℕ) (_ : NeZero k) (p : ZMod k → A), m < k ∧ (∀ j : ℕ, j ≤ m → p (j : ZMod k) = z j) ∧
      ∀ n : ZMod k, (fun j : Fin (r + 1) => p (n + (j : ℕ))) ∈ language X (r + 1) := by
  obtain ⟨m', e, he0, heL, hcons, hem⟩ := exists_edgeWalk_of_reflTransGen
    (reflTransGen_word_zero_of_mem_retainedSubshift hz (m + 1))
    (isCyclicEdge_word_of_mem_retainedSubshift hz m).1 (by rw [tail_word, Nat.cast_succ])
  let E : ℕ → Fin (r + 1) → A := fun i => if i < m then word z i (r + 1) else e (i - m)
  have hEword : ∀ i, i ≤ m → E i = word z i (r + 1) := by
    intro i hi
    rcases Nat.lt_or_ge i m with h | h
    · exact if_pos h
    · rw [show i = m by omega]
      show (if m < m then word z m (r + 1) else e (m - m)) = word z m (r + 1)
      rw [if_neg (lt_irrefl m), Nat.sub_self, he0]
  have hEL : ∀ i, i ≤ m + m' → E i ∈ language X (r + 1) := by
    intro i hi
    rcases Nat.lt_or_ge i m with h | h
    · rw [hEword i h.le]
      exact (isCyclicEdge_word_of_mem_retainedSubshift hz i).1
    · show (if i < m then word z i (r + 1) else e (i - m)) ∈ language X (r + 1)
      rw [if_neg (by omega)]
      exact heL (i - m) (by omega)
  have hEcons : ∀ i, i < m + m' → Fin.tail (E i) = Fin.init (E (i + 1)) := by
    intro i hi
    rcases Nat.lt_or_ge i m with h | h
    · rw [hEword i h.le, hEword (i + 1) h, tail_word, init_word, Nat.cast_succ]
    · show Fin.tail (if i < m then word z i (r + 1) else e (i - m)) =
        Fin.init (if i + 1 < m then word z (i + 1 : ℕ) (r + 1) else e (i + 1 - m))
      rw [if_neg (by omega), if_neg (by omega), show i + 1 - m = i - m + 1 by omega]
      exact hcons (i - m) (by omega)
  have hEwrap : Fin.tail (E (m + m')) = Fin.init (E 0) := by
    rw [hEword 0 (Nat.zero_le m), init_word]
    show Fin.tail (if m + m' < m then word z (m + m' : ℕ) (r + 1) else e (m + m' - m)) = _
    rw [if_neg (by omega), show m + m' - m = m' by omega, hem, Nat.cast_zero]
  have hE : ∀ n : ZMod (m + m' + 1), Fin.tail (E n.val) = Fin.init (E (n + 1).val) := by
    intro n
    have hn := ZMod.val_lt n
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rcases Nat.lt_or_ge n.val (m + m') with h | h
    · rw [Nat.mod_eq_of_lt (show n.val + 1 < m + m' + 1 by omega)]
      exact hEcons n.val h
    · rw [show n.val = m + m' by omega, Nat.mod_self]
      exact hEwrap
  refine ⟨m + m' + 1, inferInstance, fun n => E n.val ⟨0, by omega⟩, by omega, fun j hj => ?_,
    fun n => ?_⟩
  · show E ((j : ZMod (m + m' + 1)).val) ⟨0, by omega⟩ = z j
    rw [ZMod.val_natCast_of_lt (show j < m + m' + 1 by omega), hEword j hj, word_apply, Fin.val_mk,
      Nat.cast_zero, add_zero]
  · have h : (fun j : Fin (r + 1) => E (n + ((j : ℕ) : ZMod (m + m' + 1))).val ⟨0, by omega⟩) =
        E n.val :=
      funext fun j => edge_apply_eq_of_tail_eq_init (fun n : ZMod (m + m' + 1) => E n.val) hE n j
    show (fun j : Fin (r + 1) => E (n + ((j : ℕ) : ZMod (m + m' + 1))).val ⟨0, by omega⟩) ∈
      language X (r + 1)
    rw [h]
    exact hEL n.val (by have := ZMod.val_lt n; omega)

/-- **A finite piece of a point of `Z_r` extends to a periodic point of `Z_r`.** -/
theorem exists_periodic_agree_retainedSubshift {X : Set (ℤ → A)} {r : ℕ} {z : ℤ → A}
    (hz : z ∈ retainedSubshift X r) (m : ℕ) :
    ∃ (k : ℕ) (q : ℤ → A), 0 < k ∧ q ∈ retainedSubshift X r ∧ (∀ i : ℤ, q (i + k) = q i) ∧
      ∀ j : ℕ, j ≤ m → q j = z j := by
  obtain ⟨k, hk, p, hmk, hp0, hpL⟩ := exists_periodic_extension hz m
  refine ⟨k, fun i => p i, by omega, mem_retainedSubshift_of_forall fun i => ?_, fun i => ?_,
    fun j hj => ?_⟩
  · have hwin : word (fun i : ℤ => p (i : ZMod k)) i (r + 1) =
        fun j : Fin (r + 1) => p ((i : ZMod k) + (j : ℕ)) :=
      funext fun j => congrArg p (by simp only [Int.cast_add, Int.cast_natCast])
    rw [hwin]
    exact isCyclicEdge_window_of_periodic p hpL _
  · show p ((i + k : ℤ) : ZMod k) = p (i : ZMod k)
    rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]
  · show p (((j : ℕ) : ℤ) : ZMod k) = z j
    rw [Int.cast_natCast]
    exact hp0 j hj

/-- **`Z_r` satisfies the cycle condition** (tex 1405–1406). -/
theorem cycleCondition_retainedSubshift (X : Set (ℤ → A)) (r : ℕ) :
    CycleCondition (retainedSubshift X r) := by
  intro s w hw
  refine ⟨hw, ?_⟩
  obtain ⟨z, hz, rfl⟩ := hw
  obtain ⟨k, q, hk, hq, hper, hagree⟩ := exists_periodic_agree_retainedSubshift hz s
  have hqw : word q 0 (s + 1) = word z 0 (s + 1) := funext fun j => by
    rw [word_apply, word_apply, zero_add, hagree j (by have := j.2; omega)]
  rw [← hqw, tail_word, init_word, zero_add]
  have hk' : (1 : ℤ) + ((k - 1 : ℕ) : ℤ) = k := by omega
  have hqk : word q (k : ℤ) s = word q 0 s := funext fun j => by
    rw [word_apply, word_apply, zero_add, add_comm, hper]
  have h := reflTransGen_word (mapsTo_shift_retainedSubshift X r) hq 1 s (k - 1)
  rw [hk', hqk] at h
  exact h

/-- **`Z_r` is nonempty** (tex 1406): along a point of a nonempty subshift over a finite alphabet two
words of length `r` repeat, and the edge at the first of them is cyclic. -/
theorem retainedSubshift_nonempty [Finite A] {X : Set (ℤ → A)}
    (hX : ∀ n : ℤ, MapsTo (shift n) X X) (hne : X.Nonempty) (r : ℕ) :
    (retainedSubshift X r).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  have key : ∀ a b : ℕ, a < b → word x a r = word x b r → (retainedSubshift X r).Nonempty := by
    intro a b hab hwab
    have hcyc : IsCyclicEdge X r (word x a (r + 1)) := by
      refine ⟨word_mem_language hX hx a (r + 1), ?_⟩
      rw [tail_word, init_word, hwab]
      have h := reflTransGen_word hX hx ((a : ℤ) + 1) r (b - (a + 1))
      rw [show (a : ℤ) + 1 + ((b - (a + 1) : ℕ) : ℤ) = b by omega] at h
      exact h
    obtain ⟨k, hk, p, -, hpL⟩ := exists_periodic_of_isCyclicEdge hcyc
    refine ⟨fun i => p i, mem_retainedSubshift_of_forall fun i => ?_⟩
    have hwin : word (fun i : ℤ => p (i : ZMod k)) i (r + 1) =
        fun j : Fin (r + 1) => p ((i : ZMod k) + (j : ℕ)) :=
      funext fun j => congrArg p (by simp only [Int.cast_add, Int.cast_natCast])
    rw [hwin]
    exact isCyclicEdge_window_of_periodic p hpL _
  obtain ⟨i, j, hij, hw⟩ := Finite.exists_ne_map_eq_of_infinite fun n : ℕ => word x n r
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hw
  · exact key j i h hw.symm

end ChainCore

end GroupApproximation

#audit_axioms GroupApproximation.WordGraph.isCyclicEdge_window_of_periodic
#audit_axioms GroupApproximation.ChainCore.exists_periodic_agree_retainedSubshift
#audit_axioms GroupApproximation.ChainCore.cycleCondition_retainedSubshift
#audit_axioms GroupApproximation.ChainCore.retainedSubshift_nonempty
