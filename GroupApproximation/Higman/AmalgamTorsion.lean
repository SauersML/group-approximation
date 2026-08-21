import GroupApproximation.Higman.AmalgamPushout
import GroupApproximation.Algebra.GroupTorsionFree

/-!
# Torsion in an amalgamated free product

`Higman.BenignTorsionFree` was organized so as never to need an amalgam: every
construction there is a direct product or an HNN extension, and the repository
proves the torsion clause for both.  The one place the organization does not
reach is the *image* half of Higman's Lemma 3.3, `BenignWitness.mapEmb`, whose
witness is the amalgam `K *_G N` of the old witness with the new ambient group.
Its torsion clause is the single statement

> an amalgamated free product of torsion-free groups is torsion-free,

which is the whole cost of `Seq.TorsionFreeImageClosure`, and is what
`Higman.OperationClosureRho` and `Higman.OperationClosureTau` are waiting on.

## What is proved here

The classical argument is: an element of finite order is conjugate into a
factor, and a factor is torsion-free by hypothesis.  Both halves of the
*consequence* are proved here, and only the reduction itself is left.

* `eq_one_of_pow_eq_one_of` --- a factor has no torsion.
* `pow_ne_one_of_cyclicallyReduced` --- an element whose word is *cyclically*
  reduced (nonempty, first and last letters in different summands) has no
  trivial power.  The `n`-fold concatenation of such a word is again a word:
  its letters are unchanged, so it is still reduced and still avoids `1`, and
  the chain condition survives each junction precisely because the two ends
  lie in different summands.  Mathlib's
  `Monoid.PushoutI.Reduced.eq_empty_of_mem_range` then says its product is not
  in the base, so in particular it is not `1`.
* `reduced_toWord` --- every normal word is reduced, which is what connects
  the above to `NormalWord.equiv`.
* `isPowerTorsionFree_pushoutI` --- the theorem, from `CyclicReduction`.

## What is left

`CyclicReduction`: every element is conjugate either into a factor or to the
product of a cyclically reduced word.  This is the induction on word length
that shortens a word whose two ends lie in the *same* summand by conjugating
by its first letter --- the amalgam analogue of
`Algebra.CoprodICyclicReduction`, whose free-product version is proved in this
repository by the same move.  **Nothing inhabits it.**
-/

namespace GroupApproximation
namespace Higman
namespace AmalgamTorsion

open Monoid Monoid.CoprodI Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {H : Type*}
  [∀ i, Group (G i)] [Group H] {φ : ∀ i, H →* G i}

/-! ## 1.  Normal words are reduced -/

/-- **Every letter of a normal word avoids the base.**  A letter lies in the
transversal and is not `1`; the transversal meets the trivial coset only in
`1`, so the letter is not in the image of the base. -/
theorem reduced_toWord {d : NormalWord.Transversal φ} (w : NormalWord d) :
    Reduced φ w.toWord := by
  rintro ⟨i, g⟩ hg hmem
  have hset : g ∈ d.set i := w.normalized i g hg
  have hne : g ≠ 1 := w.toWord.ne_one _ hg
  have h1 : (((d.compl i).equiv g).2 : G i) = 1 :=
    ((d.compl i).coe_equiv_snd_eq_one_iff_mem (d.one_mem i)).2 hmem
  have h2 : (((d.compl i).equiv g).2 : G i) = g :=
    ((d.compl i).equiv_snd_eq_self_iff_mem (one_mem _)).2 hset
  exact hne (h2.symm.trans h1)

/-! ## 2.  A factor is torsion-free -/

/-- **An element of a factor with a trivial power is trivial**, when the factor
is torsion-free. -/
theorem eq_one_of_pow_eq_one_of (hφ : ∀ i, Function.Injective (φ i))
    (htf : ∀ i, IsPowerTorsionFree (G i)) (i : ι) (g : G i) (n : ℕ) (hn : 0 < n)
    (hpow : (of (φ := φ) i g) ^ n = 1) : (of (φ := φ) i g) = 1 := by
  have hgn : (of (φ := φ) i) (g ^ n) = 1 := by
    rw [map_pow]
    exact hpow
  have hg : g ^ n = 1 := by
    refine of_injective hφ i ?_
    rw [hgn, map_one]
  rw [htf i g n hn hg, map_one]

/-! ## 3.  Cyclically reduced words -/

/-- A word is cyclically reduced when it is reduced, nonempty, and its first
and last letters lie in different summands.  The last condition forces the
length to be at least two: a one-letter word has the same first and last
letter. -/
structure CyclicallyReduced (φ : ∀ i, H →* G i) (w : Word G) : Prop where
  /-- No letter is in the base. -/
  reduced : Reduced φ w
  /-- There is at least one letter. -/
  ne_nil : w.toList ≠ []
  /-- The ends lie in different summands. -/
  ends_ne : ∀ x ∈ w.toList.getLast?, ∀ y ∈ w.toList.head?, x.1 ≠ y.1

/-- The list underlying the `n`-fold concatenation of a word with itself.
Nothing here is about groups; the list lemmas are stated for an arbitrary
type. -/
def powList {α : Type*} (l : List α) : ℕ → List α
  | 0 => []
  | (n + 1) => l ++ powList l n

theorem mem_powList {α : Type*} {l : List α} {n : ℕ} {x : α}
    (hx : x ∈ powList l n) : x ∈ l := by
  induction n with
  | zero => simp [powList] at hx
  | succ m ih =>
      rw [powList, List.mem_append] at hx
      rcases hx with h | h
      · exact h
      · exact ih h

theorem head?_powList {α : Type*} {l : List α} (hl : l ≠ []) {n : ℕ} (hn : 0 < n) :
    (powList l n).head? = l.head? := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp [powList]

theorem powList_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) {n : ℕ} (hn : 0 < n) :
    powList l n ≠ [] := by
  intro hc
  have h := head?_powList hl hn
  rw [hc] at h
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp at h

theorem getLast?_append_of_ne_nil {α : Type*} (l : List α) {m : List α} (hm : m ≠ []) :
    (l ++ m).getLast? = m.getLast? := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil =>
          obtain ⟨b, s, rfl⟩ := List.exists_cons_of_ne_nil hm
          simp
      | cons c u =>
          rw [List.cons_append, List.cons_append, List.getLast?_cons_cons,
            ← List.cons_append]
          exact ih

theorem getLast?_powList {α : Type*} {l : List α} (hl : l ≠ []) {n : ℕ} (hn : 0 < n) :
    (powList l n).getLast? = l.getLast? := by
  induction n with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [powList]
      · rw [powList, getLast?_append_of_ne_nil _ (powList_ne_nil hl hm)]
        exact ih hm

theorem isChain_powList {α : Type*} {R : α → α → Prop} {l : List α} (hl : l ≠ [])
    (hchain : l.IsChain R)
    (hcyc : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y) (n : ℕ) :
    (powList l n).IsChain R := by
  induction n with
  | zero => simp [powList]
  | succ m ih =>
      rw [powList]
      refine List.IsChain.append hchain ih ?_
      intro x hx y hy
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [powList] at hy
      · rw [head?_powList hl hm] at hy
        exact hcyc x hx y hy

theorem prod_powList (l : List (Σ i, G i)) (n : ℕ) :
    ((powList l n).map fun x : Σ i, G i => CoprodI.of x.snd).prod
      = ((l.map fun x : Σ i, G i => CoprodI.of x.snd).prod) ^ n := by
  induction n with
  | zero => simp [powList]
  | succ m ih =>
      rw [powList, List.map_append, List.prod_append, ih, pow_succ']

/-- The `n`-fold concatenation of a cyclically reduced word with itself. -/
def powWord {w : Word G} (hw : CyclicallyReduced φ w) (n : ℕ) : Word G where
  toList := powList w.toList n
  ne_one := fun _ hx => w.ne_one _ (mem_powList hx)
  chain_ne := isChain_powList hw.ne_nil w.chain_ne hw.ends_ne n

theorem prod_powWord {w : Word G} (hw : CyclicallyReduced φ w) (n : ℕ) :
    (powWord hw n).prod = w.prod ^ n := prod_powList _ _

theorem reduced_powWord {w : Word G} (hw : CyclicallyReduced φ w) (n : ℕ) :
    Reduced φ (powWord hw n) := fun _ hx => hw.reduced _ (mem_powList hx)

/-- **A cyclically reduced word has no trivial power.** -/
theorem pow_ne_one_of_cyclicallyReduced (hφ : ∀ i, Function.Injective (φ i))
    {w : Word G} (hw : CyclicallyReduced φ w) {n : ℕ} (hn : 0 < n) :
    (ofCoprodI w.prod : PushoutI φ) ^ n ≠ 1 := by
  intro hpow
  have hmem : (ofCoprodI (powWord hw n).prod : PushoutI φ) ∈ (base φ).range := by
    rw [prod_powWord, map_pow, hpow]
    exact one_mem _
  have hempty := (reduced_powWord hw n).eq_empty_of_mem_range hφ hmem
  have hnil : powList w.toList n = [] := congrArg Word.toList hempty
  exact powList_ne_nil hw.ne_nil hn hnil

/-! ## 4.  The theorem, from cyclic reduction -/

/-- **Input: cyclic reduction.**  Every element of an amalgam is conjugate
either into a factor or to the product of a cyclically reduced word.

**Nothing inhabits this.** -/
def CyclicReduction (φ : ∀ i, H →* G i) : Prop :=
  ∀ x : PushoutI φ,
    (∃ (c : PushoutI φ) (i : ι) (g : G i), x = c * of i g * c⁻¹) ∨
    (∃ (c : PushoutI φ) (w : Word G), CyclicallyReduced φ w ∧
      x = c * ofCoprodI w.prod * c⁻¹)

theorem pow_eq_one_of_conj {c y : PushoutI φ} {n : ℕ}
    (h : (c * y * c⁻¹) ^ n = 1) : y ^ n = 1 := by
  have h1 : (MulAut.conj c) (y ^ n) = 1 := by
    rw [map_pow]
    exact h
  refine (MulAut.conj c).injective ?_
  rw [h1, map_one]

/-- **An amalgamated free product of torsion-free groups is torsion-free**,
given cyclic reduction. -/
theorem isPowerTorsionFree_pushoutI (hφ : ∀ i, Function.Injective (φ i))
    (htf : ∀ i, IsPowerTorsionFree (G i)) (hcr : CyclicReduction φ) :
    IsPowerTorsionFree (PushoutI φ) := by
  intro x n hn hxn
  rcases hcr x with ⟨c, i, g, rfl⟩ | ⟨c, w, hw, rfl⟩
  · rw [eq_one_of_pow_eq_one_of hφ htf i g n hn (pow_eq_one_of_conj hxn)]
    group
  · exact absurd (pow_eq_one_of_conj hxn)
      (pow_ne_one_of_cyclicallyReduced hφ hw hn)

end AmalgamTorsion
end Higman
end GroupApproximation
