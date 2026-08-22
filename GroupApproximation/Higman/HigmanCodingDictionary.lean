import GroupApproximation.Higman.EnumeratedRangeTrace
import GroupApproximation.Higman.GeneratedEnumeration
import GroupApproximation.Computability.WordProblemRE

/-!
# The coding dictionary: window coordinates, codes, and ℕ-indexed computability

Higman's relations live on `Seq.E = ℤ →₀ ℤ` and are cut out by conditions on a
finite window; Mathlib's computability lives on `ℕ` through `Primcodable`.  This
module is the dictionary between the two, built once so that no later work item
has to rebuild it.

## The three layers

* **Codes.**  A sequence is coded by a list of index/value pairs
  (`Higman.seqOfList`), and `Higman.REset` reads recursive enumerability off the
  codes.  `Seq.evalCode` is the *explicit computable function* that evaluates a
  code at one index, and `Seq.seqOfList_apply` identifies it with `seqOfList`.
  Everything computable below is phrased in terms of `evalCode`, never in terms
  of the noncomputable `seqOfList`.
* **Coordinates.**  `Seq.windowCoords n f : Fin n → ℤ` reads the window
  `[0, n)` of a sequence, `Seq.coordSeq n v` writes it back, and
  `Seq.windowEquiv n` is the resulting bijection
  `(Fin n → ℤ) ≃ Seq.windowSupport n`.  This is the arity-`n` interface: a
  relation of arity `n` is a predicate on `Fin n → ℤ`, and `Seq.CoordHigman` is
  its Higman-generation.
* **Transfer.**  `Seq.REset_window_iff` says that a window-supported set is
  recursively enumerable exactly when its tuple of coordinates is, and
  `Seq.boundedWindowRE_iff_coord` restates the hypothesis of
  `Higman.BoundedWindowRE` purely in arity-`n` terms.

## The intersection convention

Every window-supported set here is written `{f | R f} ∩ Seq.windowSupport n`,
with the condition **first**.  That is not cosmetic: `A ∩ B` and `B ∩ A` are
equal but not definitionally equal, so the order is what makes this set
*definitionally* `Seq.restrictArity n {f | R f}` in
`Higman.HigmanVariableCalculus`.  With the orders agreeing, the two layers meet
by `Iff.rfl` and that file's `Seq.restrictArity_inter` and
`Seq.restrictArity_union` apply to these sets; with them disagreeing, every
seam would carry a `Set.inter_comm`.  This module does **not** import the
variable calculus — the coding layer is the foundation of the fan-out and must
not go red when a module above it does — so the one-line bridge belongs in
whichever file first needs both.

## Why the window test compares against a list of constants

`Seq.windowSupport n` is the condition `0 ≤ j < n` on the indices, and the
obvious way to decide it is the order on `ℤ`.  That is not available: pinned
Mathlib has **no** declaration mentioning both `Int` and `Primrec`, so there is
no primitive-recursive order, addition, or cast on `ℤ` to build on.  What every
`Primcodable` type does have is `Primrec.eq`.  `Seq.inWindowIdx` therefore
decides `0 ≤ j < n` by comparing `j` against the *fixed list* `Seq.windowIdx n`
of the `n` window indices, which needs equality only.  The same device is what
makes `Seq.primrec_listOfCoords` go through with no cast on `ℤ`: the index of
each slot is a constant of the slot, so `Primrec.list_ofFn` supplies it by
`Primrec.const`.

## The one arithmetic input

Summing the values a code puts at one index is the single place where `ℤ`
arithmetic is unavoidable, and it is the single place this module takes a
hypothesis: `Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)`, written `hadd` throughout.  It is
true, and it is a gap in Mathlib rather than in Higman: `Primcodable ℤ` is
`Primcodable.ofDenumerable` through `Equiv.intEquivNat`, under which

    Encodable.encode (Int.ofNat k) = 2 * k ,   Encodable.encode (Int.negSucc k) = 2 * k + 1 ,

so `hadd` is `Primrec.encode_iff` applied to the `ℕ`-valued function of the two
encodings that reads, by parity of `m` and `k`,

    both even → m + k ,      both odd → m + k + 1 ,
    m even, k odd → if k < m then m - k - 1 else k - m ,
    m odd, k even → if m < k then k - m - 1 else m - k ,

every branch of which is `Primrec.nat_add`, `Primrec.nat_sub`,
`Primrec.nat_mod`, `Primrec.nat_lt` and `Primrec.ite`.  Discharging it once
discharges it for the whole fan-out, and `Seq.primrec_natCast_int` below is the
first thing it buys.

Nothing else in this module is open: the coordinate bijection, the identities
for `evalCode`, the window test and both directions of the transfer are proved.

## ℤ against ℕ

`ℤ` is `Denumerable`, so `Seq.primrec_int_encode` and `Seq.primrec_int_ofNat`
are the two primitive-recursive directions of the sign encoding and
`Seq.primrec_int_iff` turns any `ℤ`-indexed `Primrec` question into a
`ℕ`-indexed one.  These are unconditional; they need no arithmetic and hence not
`hadd`.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  Codes, evaluated

`seqOfList` is noncomputable, being a finite sum in `ℤ →₀ ℤ`.  `evalCode` is the
function of the code that computes the same value, and it is the only form the
computability arguments below ever see. -/

/-- The value a code puts at one index. -/
def evalCode (l : List (ℤ × ℤ)) (j : ℤ) : ℤ :=
  (l.map fun p => if p.1 = j then p.2 else 0).sum

theorem evalCode_nil (j : ℤ) : evalCode [] j = 0 := by
  simp [evalCode]

theorem evalCode_cons (p : ℤ × ℤ) (l : List (ℤ × ℤ)) (j : ℤ) :
    evalCode (p :: l) j = (if p.1 = j then p.2 else 0) + evalCode l j := by
  simp [evalCode]

/-- **The coding dictionary at one index.**  A coded sequence and its code
evaluate to the same integer. -/
theorem seqOfList_apply (l : List (ℤ × ℤ)) (j : ℤ) : seqOfList l j = evalCode l j := by
  induction l with
  | nil => simp [seqOfList, evalCode]
  | cons p l ih =>
      have hcons : seqOfList (p :: l) = Finsupp.single p.1 p.2 + seqOfList l := by
        simp [seqOfList]
      rw [hcons, Finsupp.add_apply, ih, Finsupp.single_apply, evalCode_cons]

/-- A code contributes nothing at an index it does not mention. -/
theorem evalCode_eq_zero_of_not_mem {l : List (ℤ × ℤ)} {j : ℤ}
    (h : ∀ p ∈ l, p.1 ≠ j) : evalCode l j = 0 := by
  induction l with
  | nil => exact evalCode_nil j
  | cons p l ih =>
      have hp : p.1 ≠ j := h p (List.mem_cons_self ..)
      have ht : evalCode l j = 0 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
      rw [evalCode_cons, if_neg hp, ht, add_zero]

/-! ### Folds

`Primrec.list_foldr` is the only fold Mathlib exposes, while `List.sum`,
`List.all` and `List.any` are the forms the algebra wants.  These three lemmas
are the bridge, and they are stated without reference to how the library happens
to define the three. -/

theorem list_sum_eq_foldr (l : List ℤ) : l.sum = l.foldr (fun b s => b + s) 0 := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.sum_cons, ih, List.foldr_cons]

theorem list_all_eq_foldr {α : Type*} (p : α → Bool) (l : List α) :
    l.all p = (l.map p).foldr (fun b s => b && s) true := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem list_any_eq_foldr {α : Type*} (p : α → Bool) (l : List α) :
    l.any p = (l.map p).foldr (fun b s => b || s) false := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-! ## 2.  Window coordinates

The window `[0, n)` of a sequence is an `n`-tuple of integers, and every
`n`-tuple is the window of exactly one window-supported sequence.  This is the
arity-`n` interface every later work item speaks. -/

/-- The code of the sequence with prescribed values on the window `[0, n)`.
The index of a slot is a constant of the slot, which is what makes this
primitive recursive without a cast `ℕ → ℤ`. -/
def listOfCoords (n : ℕ) (v : Fin n → ℤ) : List (ℤ × ℤ) :=
  List.ofFn fun i : Fin n => (((i : ℕ) : ℤ), v i)

/-- The sequence with prescribed values on the window `[0, n)`. -/
noncomputable def coordSeq (n : ℕ) (v : Fin n → ℤ) : E := seqOfList (listOfCoords n v)

/-- The window coordinates of a sequence. -/
def windowCoords (n : ℕ) (f : E) : Fin n → ℤ := fun i => f ((i : ℕ) : ℤ)

theorem windowCoords_mk (n : ℕ) (f : E) (m : ℕ) (hm : m < n) :
    windowCoords n f ⟨m, hm⟩ = f (m : ℤ) := rfl

theorem coordSeq_apply (n : ℕ) (v : Fin n → ℤ) (j : ℤ) :
    coordSeq n v j = ∑ i : Fin n, (if ((i : ℕ) : ℤ) = j then v i else 0) := by
  have h1 : coordSeq n v j = evalCode (listOfCoords n v) j := seqOfList_apply _ _
  have h2 : ((List.ofFn fun i : Fin n => (((i : ℕ) : ℤ), v i)).map
      fun p : ℤ × ℤ => if p.1 = j then p.2 else 0)
      = List.ofFn fun i : Fin n => (if ((i : ℕ) : ℤ) = j then v i else 0) :=
    List.map_ofFn
  rw [h1]
  show ((List.ofFn fun i : Fin n => (((i : ℕ) : ℤ), v i)).map
    fun p : ℤ × ℤ => if p.1 = j then p.2 else 0).sum = _
  rw [h2, List.sum_ofFn]

theorem coordSeq_apply_natCast (n : ℕ) (v : Fin n → ℤ) (m : ℕ) (hm : m < n) :
    coordSeq n v (m : ℤ) = v ⟨m, hm⟩ := by
  rw [coordSeq_apply]
  refine (Finset.sum_eq_single (⟨m, hm⟩ : Fin n) ?_ ?_).trans ?_
  · intro i _ hi
    refine if_neg fun h => hi ?_
    have hval : (i : ℕ) = m := by exact_mod_cast h
    exact Fin.val_injective hval
  · intro h
    exact absurd (Finset.mem_univ (⟨m, hm⟩ : Fin n)) h
  · simp

theorem coordSeq_apply_of_outside (n : ℕ) (v : Fin n → ℤ) (j : ℤ)
    (hj : ∀ k : Fin n, ((k : ℕ) : ℤ) ≠ j) : coordSeq n v j = 0 := by
  rw [coordSeq_apply]
  exact Finset.sum_eq_zero fun i _ => if_neg (hj i)

/-- **Appending a last variable.**  Writing a tuple back after `Fin.snoc` adds a
single coordinate at index `n`.  This is the bridge to the quantifier layer: the
carrier-free characterizations there (`Seq.mem_existsLast_iff`,
`Seq.mem_padLast_iff`, `Seq.mem_existsAt_iff` in
`Higman.HigmanVariableCalculus`) speak only of `f + Finsupp.single (n : ℤ) y`,
so this identity transports all of them to `Fin n → ℤ` verbatim. -/
theorem coordSeq_snoc (n : ℕ) (v : Fin n → ℤ) (y : ℤ) :
    coordSeq (n + 1) (Fin.snoc v y) = coordSeq n v + Finsupp.single (n : ℤ) y := by
  refine Finsupp.ext fun j => ?_
  rw [Finsupp.add_apply, coordSeq_apply, coordSeq_apply, Finsupp.single_apply,
    Fin.sum_univ_castSucc]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by simp
  · simp

theorem coordSeq_mem_windowSupport (n : ℕ) (v : Fin n → ℤ) :
    coordSeq n v ∈ windowSupport n := by
  rw [mem_windowSupport_iff]
  constructor
  · intro j hj
    exact coordSeq_apply_of_outside n v j fun k => by omega
  · intro j hj
    refine coordSeq_apply_of_outside n v j fun k => ?_
    have hk : (k : ℕ) < n := k.isLt
    omega

theorem windowCoords_coordSeq (n : ℕ) (v : Fin n → ℤ) :
    windowCoords n (coordSeq n v) = v := by
  funext k
  exact coordSeq_apply_natCast n v (k : ℕ) k.isLt

theorem coordSeq_windowCoords {n : ℕ} {f : E} (hf : f ∈ windowSupport n) :
    coordSeq n (windowCoords n f) = f := by
  rw [mem_windowSupport_iff] at hf
  refine Finsupp.ext fun j => ?_
  by_cases hj0 : j < 0
  · rw [hf.1 j hj0]
    exact coordSeq_apply_of_outside n _ j fun k => by omega
  · by_cases hjn : (n : ℤ) ≤ j
    · rw [hf.2 j hjn]
      refine coordSeq_apply_of_outside n _ j fun k => ?_
      have hk : (k : ℕ) < n := k.isLt
      omega
    · have hlt : j.toNat < n := by omega
      have hj : j = ((j.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
      rw [hj, coordSeq_apply_natCast n (windowCoords n f) j.toNat hlt, windowCoords_mk]

/-- **The window is `ℤⁿ`.**  This is the arity-`n` interface, as a bijection. -/
noncomputable def windowEquiv (n : ℕ) : (Fin n → ℤ) ≃ windowSupport n where
  toFun v := ⟨coordSeq n v, coordSeq_mem_windowSupport n v⟩
  invFun f := windowCoords n (f : E)
  left_inv v := windowCoords_coordSeq n v
  right_inv f := Subtype.ext (coordSeq_windowCoords f.2)

/-- Writing back the window coordinates truncates a sequence to its window.
This is the bridge to the window operator `Seq.windowAt` the trace format uses;
on `Seq.windowSupport n` it is the identity, by `Seq.coordSeq_windowCoords`. -/
theorem coordSeq_windowCoords_eq_windowAt (n : ℕ) (f : E) :
    coordSeq n (windowCoords n f) = windowAt n 0 f := by
  refine Finsupp.ext fun j => ?_
  rw [windowAt_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (n : ℤ)
  · obtain ⟨hj0, hjn⟩ := Finset.mem_Ico.mp hj
    rw [if_pos hj]
    have hlt : j.toNat < n := by omega
    have hje : j = ((j.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hj0).symm
    rw [hje, coordSeq_apply_natCast n (windowCoords n f) j.toNat hlt, windowCoords_mk,
      zero_add]
  · rw [if_neg hj]
    have hj' : ¬(0 ≤ j ∧ j < (n : ℤ)) := fun hc => hj (Finset.mem_Ico.mpr hc)
    refine coordSeq_apply_of_outside n _ j fun k => ?_
    have hk : (k : ℕ) < n := k.isLt
    omega

/-- A window-supported condition is the image of its coordinate form. -/
theorem inter_windowSupport_eq_image (n : ℕ) (R : E → Prop) :
    {f | R f} ∩ windowSupport n = coordSeq n '' {v | R (coordSeq n v)} := by
  ext f
  constructor
  · rintro ⟨hR, hw⟩
    refine ⟨windowCoords n f, ?_, coordSeq_windowCoords hw⟩
    show R (coordSeq n (windowCoords n f))
    rw [coordSeq_windowCoords hw]
    exact hR
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv, coordSeq_mem_windowSupport n v⟩

theorem image_coordSeq_preimage {n : ℕ} {B : Set E} (hB : B ⊆ windowSupport n) :
    coordSeq n '' {v | coordSeq n v ∈ B} = B := by
  ext f
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hf
    refine ⟨windowCoords n f, ?_, coordSeq_windowCoords (hB hf)⟩
    show coordSeq n (windowCoords n f) ∈ B
    rw [coordSeq_windowCoords (hB hf)]
    exact hf

theorem inter_setOf_mem_eq {n : ℕ} {B : Set E} (hB : B ⊆ windowSupport n) :
    {f | f ∈ B} ∩ windowSupport n = B := by
  ext f
  exact ⟨fun h => h.1, fun h => ⟨h, hB h⟩⟩

/-! ## 3.  Generation, on the window and in coordinates -/

/-- **Higman-generation of a window-supported condition.**  Only the values of
`R` on sequences supported in `[0, n)` enter.

The intersection is written with the condition **first**, so that this set is
*definitionally* `Seq.restrictArity n {f | R f}` in
`Higman.HigmanVariableCalculus` — `A ∩ B` and `B ∩ A` are equal but not defeq,
so the order is what makes the two layers compose without a `Set.inter_comm` at
every seam. -/
def WindowHigman (n : ℕ) (R : E → Prop) : Prop :=
  HigmanGenerated ({f | R f} ∩ windowSupport n)

/-- **`WindowHigman` sees only the window.** -/
theorem windowHigman_congr {n : ℕ} {R R' : E → Prop}
    (h : ∀ f ∈ windowSupport n, (R f ↔ R' f)) : WindowHigman n R ↔ WindowHigman n R' := by
  have hset : {f | R f} ∩ windowSupport n = {f | R' f} ∩ windowSupport n := by
    ext f
    constructor
    · rintro ⟨hR, hw⟩
      exact ⟨(h f hw).mp hR, hw⟩
    · rintro ⟨hR, hw⟩
      exact ⟨(h f hw).mpr hR, hw⟩
  unfold WindowHigman
  rw [hset]

/-- **Higman-generation of a relation of arity `n`.**  This is the shape the
fan-out speaks: an arity-`n` relation is a predicate on `Fin n → ℤ`. -/
def CoordHigman (n : ℕ) (P : (Fin n → ℤ) → Prop) : Prop :=
  HigmanGenerated (coordSeq n '' {v | P v})

theorem coordHigman_iff (n : ℕ) (P : (Fin n → ℤ) → Prop) :
    CoordHigman n P ↔ WindowHigman n fun f => P (windowCoords n f) := by
  have hkey : {f | P (windowCoords n f)} ∩ windowSupport n = coordSeq n '' {v | P v} := by
    ext f
    constructor
    · rintro ⟨hR, hw⟩
      exact ⟨windowCoords n f, hR, coordSeq_windowCoords hw⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, coordSeq_mem_windowSupport n v⟩
      show P (windowCoords n (coordSeq n v))
      rw [windowCoords_coordSeq]
      exact hv
  unfold CoordHigman WindowHigman
  rw [hkey]

/-! ### Membership, in applied form

Membership in `{f | R f} ∩ windowSupport n` and in `coordSeq n '' {v | P v}` is
*definitionally* the applied predicate but not *syntactically*, so `rw` and
`simp` at such a hypothesis find no occurrence.  These three restate the two
sets this module exports with the predicate applied; rewrite by them before
destructuring. -/

theorem mem_inter_windowSupport_iff (n : ℕ) (R : E → Prop) (f : E) :
    f ∈ {g | R g} ∩ windowSupport n ↔ R f ∧ f ∈ windowSupport n := Iff.rfl

theorem mem_coordSeq_image_iff (n : ℕ) (P : (Fin n → ℤ) → Prop) (f : E) :
    f ∈ coordSeq n '' {v | P v} ↔ ∃ v, P v ∧ coordSeq n v = f :=
  Set.mem_image _ _ _

/-! ### Sets against tuples

A work item that carries an arity-`n` relation as a *set* `B` of sequences with
`B ⊆ windowSupport n` — which is the same condition as `Seq.IsArity n B` in
`Higman.HigmanVariableCalculus`, that being a plain subset statement — meets the
tuple form here through `coordsOf`. -/

/-- The arity-`n` predicate on tuples attached to a window-supported set. -/
def coordsOf (n : ℕ) (B : Set E) : (Fin n → ℤ) → Prop := fun v => coordSeq n v ∈ B

theorem mem_coordsOf_iff (n : ℕ) (B : Set E) (v : Fin n → ℤ) :
    coordsOf n B v ↔ coordSeq n v ∈ B := Iff.rfl

/-- **Generation transfers between the two forms.** -/
theorem coordHigman_coordsOf_iff {n : ℕ} {B : Set E} (hB : B ⊆ windowSupport n) :
    CoordHigman n (coordsOf n B) ↔ HigmanGenerated B := by
  unfold CoordHigman coordsOf
  rw [image_coordSeq_preimage hB]

/-! ## 4.  ℤ against ℕ

`ℤ` is `Denumerable`, so the sign encoding is already primitive recursive in
both directions and any `ℤ`-indexed question is a `ℕ`-indexed one.  None of this
needs arithmetic. -/

theorem primrec_int_encode : Primrec (Encodable.encode : ℤ → ℕ) := Primrec.encode

theorem primrec_int_ofNat : Primrec (Denumerable.ofNat ℤ) := Primrec.ofNat ℤ

/-- **The sign encoding, as a transfer principle.**  A function of an integer is
primitive recursive exactly when its `ℕ`-indexed form is. -/
theorem primrec_int_iff {σ : Type} [Primcodable σ] {f : ℤ → σ} :
    Primrec f ↔ Primrec fun m : ℕ => f (Denumerable.ofNat ℤ m) := by
  constructor
  · intro h
    exact h.comp (Primrec.ofNat ℤ)
  · intro h
    have henc : Primrec (Encodable.encode : ℤ → ℕ) := Primrec.encode
    exact (h.comp henc).of_eq fun a => by rw [Denumerable.ofNat_encode]

/-- The cast `ℕ → ℤ`, which pinned Mathlib does not have either.  It is the
first thing `hadd` buys, and it is what lets a later work item move a
`ℕ`-indexed construction onto the index line. -/
theorem primrec_natCast_int (hadd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)) :
    Primrec (fun m : ℕ => (m : ℤ)) := by
  have hrec : Primrec fun m : ℕ =>
      Nat.rec (motive := fun _ => ℤ) 0 (fun _ ih => ih + 1) m :=
    Primrec.nat_rec' (h := fun (_ : ℕ) (p : ℕ × ℤ) => p.2 + 1) Primrec.id
      (Primrec.const (0 : ℤ))
      (hadd.comp (Primrec.snd.comp Primrec.snd) (Primrec.const (1 : ℤ)))
  refine hrec.of_eq fun m => ?_
  induction m with
  | zero => rfl
  | succ k ih =>
      show (Nat.rec (motive := fun _ => ℤ) 0 (fun _ ih => ih + 1) k) + 1 = ((k + 1 : ℕ) : ℤ)
      rw [ih]
      omega

/-! ## 5.  The codes, computably

Everything here is a statement about the explicit functions `evalCode`,
`inWindowIdx`, `windowCheck` and `decodeCoords`; `hadd` is the only input. -/

/-- The `n` indices of the window `[0, n)`, as a fixed list of integers. -/
def windowIdx (n : ℕ) : List ℤ := List.ofFn fun i : Fin n => ((i : ℕ) : ℤ)

theorem mem_windowIdx_iff (n : ℕ) (j : ℤ) :
    j ∈ windowIdx n ↔ 0 ≤ j ∧ j < (n : ℤ) := by
  rw [show windowIdx n = List.ofFn fun i : Fin n => ((i : ℕ) : ℤ) from rfl, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    have hi : (i : ℕ) < n := i.isLt
    omega
  · rintro ⟨h0, hn⟩
    have hlt : j.toNat < n := by omega
    exact ⟨⟨j.toNat, hlt⟩, Int.toNat_of_nonneg h0⟩

/-- Whether an index lies in the window, decided by comparing it against the
fixed list `windowIdx n`.

Deciding `0 ≤ j < n` directly would ask for the order on `ℤ` to be primitive
recursive, which pinned Mathlib does not provide.  Comparing against finitely
many constants asks only for `Primrec.eq`, which every `Primcodable` type
has. -/
def inWindowIdx (n : ℕ) (j : ℤ) : Bool := (windowIdx n).any fun a => decide (a = j)

theorem inWindowIdx_eq_true_iff (n : ℕ) (j : ℤ) :
    inWindowIdx n j = true ↔ 0 ≤ j ∧ j < (n : ℤ) := by
  rw [show inWindowIdx n j = (windowIdx n).any (fun a => decide (a = j)) from rfl,
    List.any_eq_true, ← mem_windowIdx_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    rw [decide_eq_true_iff] at hb
    rw [← hb]
    exact ha
  · intro h
    exact ⟨j, h, by simp⟩

/-- The window test, on codes.  A code lands in the window exactly when every
index it mentions is either inside the window or carries the value zero. -/
def windowCheck (n : ℕ) (l : List (ℤ × ℤ)) : Bool :=
  l.all fun p => inWindowIdx n p.1 || decide (evalCode l p.1 = 0)

theorem windowCheck_eq_true_iff (n : ℕ) (l : List (ℤ × ℤ)) :
    windowCheck n l = true ↔ seqOfList l ∈ windowSupport n := by
  rw [mem_windowSupport_iff]
  constructor
  · intro h
    have h' : ∀ p ∈ l, inWindowIdx n p.1 = true ∨ evalCode l p.1 = 0 := by
      intro p hp
      have hp' := (List.all_eq_true.mp h) p hp
      rw [Bool.or_eq_true, decide_eq_true_iff] at hp'
      exact hp'
    have key : ∀ j : ℤ, ¬(0 ≤ j ∧ j < (n : ℤ)) → seqOfList l j = 0 := by
      intro j hj
      by_cases hmem : ∃ p ∈ l, p.1 = j
      · obtain ⟨p, hp, rfl⟩ := hmem
        rcases h' p hp with hin | hz
        · exact absurd ((inWindowIdx_eq_true_iff n p.1).mp hin) hj
        · rw [seqOfList_apply]
          exact hz
      · rw [seqOfList_apply]
        exact evalCode_eq_zero_of_not_mem fun p hp hpj => hmem ⟨p, hp, hpj⟩
    exact ⟨fun i hi => key i (by omega), fun i hi => key i (by omega)⟩
  · intro h
    refine List.all_eq_true.mpr fun p hp => ?_
    rw [Bool.or_eq_true, decide_eq_true_iff]
    by_cases hin : 0 ≤ p.1 ∧ p.1 < (n : ℤ)
    · exact Or.inl ((inWindowIdx_eq_true_iff n p.1).mpr hin)
    · refine Or.inr ?_
      rw [← seqOfList_apply]
      rcases not_and_or.mp hin with hc | hc
      · exact h.1 p.1 (by omega)
      · exact h.2 p.1 (by omega)

/-- The window coordinates of a coded sequence, read off the code. -/
def decodeCoords (n : ℕ) (l : List (ℤ × ℤ)) : Fin n → ℤ :=
  fun i => evalCode l ((i : ℕ) : ℤ)

theorem decodeCoords_eq (n : ℕ) (l : List (ℤ × ℤ)) :
    decodeCoords n l = windowCoords n (seqOfList l) := by
  funext i
  exact (seqOfList_apply l _).symm

/-! ### The primitive recursion

`hadd` enters here and nowhere else. -/

theorem primrec_evalCode (hadd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)) : Primrec₂ evalCode := by
  have hmap : Primrec fun q : List (ℤ × ℤ) × ℤ =>
      q.1.map fun p : ℤ × ℤ => if p.1 = q.2 then p.2 else 0 :=
    Primrec.list_map Primrec.fst
      (Primrec.ite
        (PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)
        (Primrec.const (0 : ℤ)))
  have hfold := Primrec.list_foldr hmap (Primrec.const (0 : ℤ))
    (hadd.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact hfold.of_eq fun q => (list_sum_eq_foldr _).symm

theorem primrec_inWindowIdx (n : ℕ) : Primrec (inWindowIdx n) := by
  have hmap : Primrec fun j : ℤ => (windowIdx n).map fun a : ℤ => decide (a = j) :=
    Primrec.list_map (Primrec.const (windowIdx n))
      (PrimrecRel.comp Primrec.eq Primrec.snd Primrec.fst).decide
  have hfold := Primrec.list_foldr hmap (Primrec.const false)
    (Primrec.or.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact hfold.of_eq fun j => (list_any_eq_foldr _ _).symm

theorem primrec_windowCheck (hadd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)) (n : ℕ) :
    Primrec (windowCheck n) := by
  have hev := primrec_evalCode hadd
  have hmap : Primrec fun l : List (ℤ × ℤ) =>
      l.map fun p : ℤ × ℤ => inWindowIdx n p.1 || decide (evalCode l p.1 = 0) :=
    Primrec.list_map Primrec.id
      (Primrec.or.comp
        ((primrec_inWindowIdx n).comp (Primrec.fst.comp Primrec.snd))
        (PrimrecRel.comp Primrec.eq
          (hev.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
          (Primrec.const (0 : ℤ))).decide)
  have hfold := Primrec.list_foldr hmap (Primrec.const true)
    (Primrec.and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact hfold.of_eq fun l => (list_all_eq_foldr _ _).symm

theorem primrec_decodeCoords (hadd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)) (n : ℕ) :
    Primrec (decodeCoords n) := by
  have hev := primrec_evalCode hadd
  have hi : Primrec₂ fun (i : Fin n) (l : List (ℤ × ℤ)) => evalCode l ((i : ℕ) : ℤ) :=
    Primrec.fin_curry₁.2 fun i => hev.comp Primrec.id (Primrec.const (((i : ℕ) : ℤ)))
  exact Primrec.fin_curry.2 (Primrec.comp hi (Primrec.pair Primrec.snd Primrec.fst))

/-- The coordinate code of a tuple is primitive recursive, with **no** cast on
`ℤ`: the index of each slot is a constant of the slot, supplied by
`Primrec.const` under `Primrec.list_ofFn`. -/
theorem primrec_listOfCoords (n : ℕ) : Primrec (listOfCoords n) :=
  Primrec.list_ofFn fun i =>
    Primrec.pair (Primrec.const (((i : ℕ) : ℤ)))
      (Primrec.fin_app.comp Primrec.id (Primrec.const i))

theorem seqOfList_listOfCoords (n : ℕ) (v : Fin n → ℤ) :
    seqOfList (listOfCoords n v) = coordSeq n v := rfl

/-! ## 6.  The transfer -/

/-- **The transfer, forward.**  If a window-supported condition is recursively
enumerable on codes, its arity-`n` form is recursively enumerable on tuples.
This direction needs no arithmetic. -/
theorem rePred_coords_of_REset {n : ℕ} {R : E → Prop}
    (h : REset ({f | R f} ∩ windowSupport n)) :
    REPred fun v : Fin n → ℤ => R (coordSeq n v) := by
  have h' : REPred fun l : List (ℤ × ℤ) =>
      seqOfList l ∈ {f | R f} ∩ windowSupport n := h
  obtain ⟨F, hF, hspec⟩ := exists_primrec_of_rePred h'
  have hg : Primrec₂ fun (v : Fin n → ℤ) (m : ℕ) => F (listOfCoords n v) m :=
    hF.comp ((primrec_listOfCoords n).comp Primrec.fst) Primrec.snd
  refine (WordProblemRE.rePred_exists_eq_true hg.to_comp).of_eq fun v => ?_
  show (∃ m : ℕ, F (listOfCoords n v) m = true) ↔ R (coordSeq n v)
  rw [← hspec (listOfCoords n v)]
  constructor
  · rintro ⟨hR, _⟩
    exact hR
  · intro hR
    exact ⟨hR, coordSeq_mem_windowSupport n v⟩

/-- **The transfer, backward.**  If the arity-`n` form is recursively
enumerable on tuples, the window-supported condition is recursively enumerable
on codes.  This is the direction that decodes, and the only one that needs
`hadd`. -/
theorem REset_of_rePred_coords (hadd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)) {n : ℕ}
    {R : E → Prop} (h : REPred fun v : Fin n → ℤ => R (coordSeq n v)) :
    REset ({f | R f} ∩ windowSupport n) := by
  obtain ⟨F, hF, hspec⟩ := exists_primrec_of_rePred h
  have hg : Primrec₂ fun (l : List (ℤ × ℤ)) (m : ℕ) =>
      windowCheck n l && F (decodeCoords n l) m :=
    Primrec.and.comp ((primrec_windowCheck hadd n).comp Primrec.fst)
      (hF.comp ((primrec_decodeCoords hadd n).comp Primrec.fst) Primrec.snd)
  have hre := WordProblemRE.rePred_exists_eq_true hg.to_comp
  show REPred fun l : List (ℤ × ℤ) => seqOfList l ∈ {f | R f} ∩ windowSupport n
  refine hre.of_eq fun l => ?_
  show (∃ m : ℕ, (windowCheck n l && F (decodeCoords n l) m) = true) ↔
    seqOfList l ∈ {f | R f} ∩ windowSupport n
  constructor
  · rintro ⟨m, hm⟩
    rw [Bool.and_eq_true] at hm
    have hw : seqOfList l ∈ windowSupport n := (windowCheck_eq_true_iff n l).mp hm.1
    refine ⟨?_, hw⟩
    have hR : R (coordSeq n (decodeCoords n l)) := (hspec _).mpr ⟨m, hm.2⟩
    rwa [decodeCoords_eq, coordSeq_windowCoords hw] at hR
  · rintro ⟨hR, hw⟩
    have hR' : R (coordSeq n (decodeCoords n l)) := by
      rw [decodeCoords_eq, coordSeq_windowCoords hw]
      exact hR
    obtain ⟨m, hm⟩ := (hspec _).mp hR'
    refine ⟨m, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨(windowCheck_eq_true_iff n l).mpr hw, hm⟩

/-- **The coding dictionary.**  Recursive enumerability of a window-supported
condition, read on codes, is recursive enumerability of its arity-`n` form, read
on tuples over the `Primcodable` type `Fin n → ℤ`. -/
theorem REset_window_iff (hadd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)) (n : ℕ) (R : E → Prop) :
    REset ({f | R f} ∩ windowSupport n) ↔ REPred fun v : Fin n → ℤ => R (coordSeq n v) :=
  ⟨rePred_coords_of_REset, REset_of_rePred_coords hadd⟩

/-- **Recursive enumerability transfers between the two forms.**  With
`Seq.coordHigman_coordsOf_iff`, this is the whole set-against-tuple dictionary
for a work item that carries its arity-`n` relation as a subset of
`Seq.windowSupport n`. -/
theorem rePred_coordsOf_iff (hadd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)) {n : ℕ} {B : Set E}
    (hB : B ⊆ windowSupport n) : REPred (coordsOf n B) ↔ REset B := by
  have hset : {f | f ∈ B} ∩ windowSupport n = B := inter_setOf_mem_eq hB
  constructor
  · intro h
    have hc : REPred fun v : Fin n → ℤ => coordSeq n v ∈ B := h
    have h2 := REset_of_rePred_coords hadd (R := fun f => f ∈ B) hc
    rwa [hset] at h2
  · intro h
    show REPred fun v : Fin n → ℤ => coordSeq n v ∈ B
    refine rePred_coords_of_REset (R := fun f => f ∈ B) ?_
    rw [hset]
    exact h

/-- **`Higman.BoundedWindowRE`, in arity-`n` form.**  The hypothesis the trace
construction still asks for is exactly: every recursively enumerable relation of
arity `n` on the integers is Higman-generated.  Nothing about the sequence space
survives the translation, which is the point of this module. -/
theorem boundedWindowRE_iff_coord (hadd : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ)) :
    (∀ (n : ℕ) (B : Set E), REset B → B ⊆ windowSupport n → HigmanGenerated B)
      ↔ ∀ (n : ℕ) (P : (Fin n → ℤ) → Prop), REPred P → CoordHigman n P := by
  constructor
  · intro h n P hP
    have hre : REset ({f | P (windowCoords n f)} ∩ windowSupport n) := by
      refine REset_of_rePred_coords hadd ?_
      refine hP.of_eq fun v => ?_
      rw [windowCoords_coordSeq]
    have hgen := h n _ hre Set.inter_subset_right
    exact (coordHigman_iff n P).mpr hgen
  · intro h n B hB hsub
    have hP : REPred fun v : Fin n → ℤ => coordSeq n v ∈ B := by
      refine rePred_coords_of_REset (R := fun f => f ∈ B) ?_
      rw [inter_setOf_mem_eq hsub]
      exact hB
    have hgen := h n _ hP
    unfold CoordHigman at hgen
    rw [image_coordSeq_preimage hsub] at hgen
    exact hgen

end Seq
end Higman
end GroupApproximation
