import GroupApproximation.Sofic.SmallCancellationRouter

/-!
# Word combinatorics toward the Greendlinger gate

The router froze the small-cancellation surface with exactly one open
input: `GreendlingerGate`, the classical statement that `C'(1/6)`
families satisfy the Greendlinger conclusion.  This module lands the
letters-and-closure layer of the diagram-free attack, unconditionally:

* **Letters.**  Formal inversion of single letters, its involutivity,
  and the decoding of the reduction relation (`isReduced_step_iff`):
  an adjacent pair is admissible exactly when the second letter is not
  the formal inverse of the first.

* **Formal inversion preserves reduction and cyclic reduction**
  (`isReduced_invRev_iff`, `isCyclicallyReduced_invRev`), and
  **rotation preserves cyclic reduction**
  (`isCyclicallyReduced_rotate`) — the seam condition transported
  through the drop-append-take decomposition.

* **Symmetrization closure.**  The symmetrized family of a cyclically
  reduced relator set is closed under rotation
  (`rotate_mem_symmetrization`) and formal inversion
  (`invRev_mem_symmetrization`, via the rotation-inversion exchange
  `invRev_rotate`), with every member cyclically reduced
  (`symmetrization_isCyclicallyReduced`).

The next layers of the attack — the palindromic conjugation normal
form, the one-relator Greendlinger conclusion, and the minimal-
expression descent with the `C'(1/6)` piece bound — are recorded in
the gate's Cairn card as the remaining frontier.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Letters -/

/-- The formal inverse of a single letter. -/
def invLetter (c : α × Bool) : α × Bool := (c.1, !c.2)

@[simp] theorem invLetter_invLetter (c : α × Bool) :
    invLetter (invLetter c) = c := by
  cases c with
  | mk x b => cases b <;> rfl

theorem invLetter_injective :
    Function.Injective (invLetter (α := α)) := fun a b h => by
  have := congrArg invLetter h
  rwa [invLetter_invLetter, invLetter_invLetter] at this

@[simp] theorem invRev_singleton (c : α × Bool) :
    FreeGroup.invRev [c] = [invLetter c] := rfl

theorem invRev_cons (c : α × Bool) (t : List (α × Bool)) :
    FreeGroup.invRev (c :: t) =
      FreeGroup.invRev t ++ [invLetter c] := by
  unfold FreeGroup.invRev
  simp [invLetter]

@[simp] theorem invRev_nil :
    FreeGroup.invRev ([] : List (α × Bool)) = [] := rfl

theorem head?_invRev (w : List (α × Bool)) :
    (FreeGroup.invRev w).head? = w.getLast?.map invLetter := by
  induction w with
  | nil => rfl
  | cons c t ih =>
    rw [invRev_cons]
    cases ht : t with
    | nil => rfl
    | cons d t' =>
      rw [← ht, List.head?_append, ih]
      have hne : t ≠ [] := by rw [ht]; exact List.cons_ne_nil _ _
      have h1 : t.getLast? = some (t.getLast hne) :=
        List.getLast?_eq_some_getLast hne
      rw [List.getLast?_cons_of_ne_nil hne, h1]
      rfl

theorem getLast?_invRev (w : List (α × Bool)) :
    (FreeGroup.invRev w).getLast? = w.head?.map invLetter := by
  cases w with
  | nil => rfl
  | cons c t =>
    rw [invRev_cons, List.getLast?_concat]
    rfl

/-- The reduction relation of adjacent letters, decoded: the pair
`(a, b)` is admissible exactly when `b` is not the formal inverse of
`a`. -/
theorem isReduced_step_iff {a b : α × Bool} :
    (a.1 = b.1 → a.2 = b.2) ↔ b ≠ invLetter a := by
  obtain ⟨x, p⟩ := a
  obtain ⟨y, q⟩ := b
  by_cases h : x = y <;> cases p <;> cases q <;>
    simp [invLetter, Prod.ext_iff, h] <;> intro hc <;>
      exact h hc.symm

/-! ## Formal inversion preserves reduction -/

theorem step_flip {a b : α × Bool}
    (h : a.1 = b.1 → a.2 = b.2) : b.1 = a.1 → b.2 = a.2 := fun hba =>
  (h hba.symm).symm

theorem isReduced_invRev_iff {w : List (α × Bool)} :
    FreeGroup.IsReduced (FreeGroup.invRev w) ↔
      FreeGroup.IsReduced w := by
  show List.IsChain _ ((w.map _).reverse) ↔ List.IsChain _ w
  rw [List.isChain_reverse, List.isChain_map]
  constructor
  · intro h
    refine h.imp fun a b hab => ?_
    intro h1
    have h2 := hab h1.symm
    exact Bool.not_inj h2.symm
  · intro h
    refine h.imp fun a b hab => ?_
    intro h1
    exact congrArg Bool.not (step_flip hab h1)

theorem isCyclicallyReduced_invRev {w : List (α × Bool)}
    (h : FreeGroup.IsCyclicallyReduced w) :
    FreeGroup.IsCyclicallyReduced (FreeGroup.invRev w) := by
  refine ⟨isReduced_invRev_iff.mpr h.1, ?_⟩
  intro a ha b hb
  rw [Option.mem_def, getLast?_invRev, Option.map_eq_some_iff] at ha
  rw [Option.mem_def, head?_invRev, Option.map_eq_some_iff] at hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have hw := h.2 b' hb' a' ha'
  intro h1
  have h2 := congrArg Bool.not (hw (h1.symm))
  simpa [invLetter] using h2.symm

/-! ## Rotation preserves cyclic reduction -/

theorem isCyclicallyReduced_rotate {w : List (α × Bool)}
    (h : FreeGroup.IsCyclicallyReduced w) (n : ℕ) :
    FreeGroup.IsCyclicallyReduced (w.rotate n) := by
  rcases eq_or_ne w [] with rfl | hw
  · simp [List.rotate_nil]
  have hlen : 0 < w.length := List.length_pos_iff.mpr hw
  rw [← List.rotate_mod]
  set m := n % w.length with hm
  have hmlt : m < w.length := Nat.mod_lt _ hlen
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hm0, List.rotate_zero]
    exact h
  rw [List.rotate_eq_drop_append_take hmlt.le]
  constructor
  · refine List.isChain_append.2
      ⟨h.1.infix (List.drop_suffix _ _).isInfix,
       h.1.infix (List.take_prefix _ _).isInfix, ?_⟩
    intro x hx y hy
    rw [Option.mem_def, List.getLast?_drop, if_neg (by omega)] at hx
    rw [Option.mem_def, List.head?_take, if_neg (by omega)] at hy
    exact h.2 x hx y hy
  · intro a ha b hb
    rw [Option.mem_def, List.getLast?_append, List.getLast?_take,
      if_neg (by omega),
      List.getElem?_eq_getElem (by omega : m - 1 < w.length),
      Option.some_or, Option.or_eq_some_iff] at ha
    rw [Option.mem_def, List.head?_append, List.head?_drop,
      List.getElem?_eq_getElem hmlt, Option.some_or] at hb
    have hb' : b = w[m] := by
      injection hb with hb'
      exact hb'.symm
    have ha' : a = w[m - 1] := by
      rcases ha with ha1 | ⟨ha1, -⟩
      · injection ha1 with ha1'
        exact ha1'.symm
      · exact absurd ha1 (by simp)
    subst ha'
    subst hb'
    have hchain := List.isChain_iff_getElem.mp h.1 (m - 1)
      (by omega)
    have hmm : m - 1 + 1 = m := by omega
    simpa only [hmm] using hchain

/-! ## Symmetrization closure -/

theorem rotate_mem_symmetrization {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (hw : w ∈ symmetrization R) (n : ℕ) :
    w.rotate n ∈ symmetrization R := by
  obtain ⟨r, hr, k, h | h⟩ := hw
  · exact ⟨r, hr, k + n, Or.inl (by rw [h, List.rotate_rotate])⟩
  · exact ⟨r, hr, k + n, Or.inr (by rw [h, List.rotate_rotate])⟩

theorem symmetrization_isCyclicallyReduced {R : Set (List (α × Bool))}
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    {w : List (α × Bool)} (hw : w ∈ symmetrization R) :
    FreeGroup.IsCyclicallyReduced w := by
  obtain ⟨r, hr, k, h | h⟩ := hw
  · rw [h]
    exact isCyclicallyReduced_rotate (hcyc r hr) k
  · rw [h]
    exact isCyclicallyReduced_rotate
      (isCyclicallyReduced_invRev (hcyc r hr)) k

theorem invRev_rotate (l : List (α × Bool)) {k : ℕ}
    (hk : k ≤ l.length) :
    FreeGroup.invRev (l.rotate k) =
      (FreeGroup.invRev l).rotate (l.length - k) := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hklt
  · rw [List.rotate_length, Nat.sub_self, List.rotate_zero]
  rw [List.rotate_eq_drop_append_take hk, FreeGroup.invRev_append]
  have hsplit : FreeGroup.invRev l =
      FreeGroup.invRev (l.drop k) ++ FreeGroup.invRev (l.take k) := by
    conv_lhs => rw [← List.take_append_drop k l]
    rw [FreeGroup.invRev_append]
  rw [hsplit]
  have hlen : (FreeGroup.invRev (l.drop k)).length = l.length - k := by
    rw [FreeGroup.invRev_length, List.length_drop]
  rw [show l.length - k = (FreeGroup.invRev (l.drop k)).length from
    hlen.symm]
  rw [List.rotate_eq_drop_append_take (by simp),
    List.drop_left, List.take_left]

theorem invRev_mem_symmetrization {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (hw : w ∈ symmetrization R) :
    FreeGroup.invRev w ∈ symmetrization R := by
  obtain ⟨r, hr, k, h | h⟩ := hw
  · -- The empty relator has to be dispatched structurally, BEFORE the
    -- modular bound: `k % [].length = k % 0 = k`, so the side goal of
    -- `invRev_rotate` would read `k ≤ 0`, which is false for every
    -- `k ≥ 1`.  When `r = []` every list in sight is `[]` and there is
    -- nothing to bound.
    rcases eq_or_ne r [] with rfl | hr0
    · refine ⟨[], hr, 0, Or.inr ?_⟩
      rw [h]
      simp [FreeGroup.invRev]
    · refine ⟨r, hr, r.length - k % r.length, Or.inr ?_⟩
      rw [h, ← List.rotate_mod,
        invRev_rotate r (Nat.mod_lt _ (List.length_pos_iff.mpr hr0)).le]
  · rcases eq_or_ne (FreeGroup.invRev r) [] with hr0 | hr0
    · have hrnil : r = [] := by
        have h2 := congrArg FreeGroup.invRev hr0
        rw [FreeGroup.invRev_invRev] at h2
        simpa [FreeGroup.invRev] using h2
      refine ⟨r, hr, 0, Or.inl ?_⟩
      rw [h, hr0, hrnil]
      simp [FreeGroup.invRev]
    · refine ⟨r, hr,
        (FreeGroup.invRev r).length - k % (FreeGroup.invRev r).length,
        Or.inl ?_⟩
      rw [h, ← List.rotate_mod,
        invRev_rotate (FreeGroup.invRev r)
          (Nat.mod_lt _ (List.length_pos_iff.mpr hr0)).le,
        FreeGroup.invRev_invRev]

end SmallCancellationRouter
end GroupApproximation
