import GroupApproximation.GroupTheory.HNNBrittonCyclic
import Mathlib.Order.Lattice.Nat

/-!
# Syllable length in an HNN extension

The Bass--Serre tree of `HNNExtension G A B φ` has the left cosets of the base
copy `HNNExtension.of '' G` as its vertices, and the distance between two of
them is the number of stable letters in a Britton-reduced spelling of the
quotient.  This module builds that number and its calculus; the graph itself is
`GGT/BassSerreHNNTree.lean`.

## The definition

Mathlib's Britton lemma comes in the strong form
`HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq`: two reduced words with
the same product carry the *same list of signs*, so in particular the same
number of syllables.  Existence of one reduced spelling is
`HNNBritton.exists_hasSpelling`.  Together they say that the set

  `reducedLengths φ x = {n | some pinch-free spelling of x has n syllables}`

is a singleton, and `tLen φ x` is its infimum.

## The calculus

* `tLen_eq` --- *every* pinch-free spelling computes `tLen`.
* `tLen_eq_zero_iff` --- `tLen φ x = 0` exactly on the base copy.  This is
  Britton's lemma.
* `tLen_of_mul`, `tLen_mul_of` --- the base copy acts trivially on both sides,
  so `tLen` descends to the coset space on which the tree is built.  The right
  version is `HNNBritton.absorbLast`: no pinch condition inspects the group
  part of the final syllable.
* `tLen_mul_t_zpow_le` --- crossing one edge changes the length by at most one.
  Either the new syllable survives, and the spelling grows by one, or it
  pinches against the final syllable of the old one, and the spelling shrinks
  by one.  This single case split is the engine of the whole development: it
  reappears in `BassSerreHNNTree.step` as the uniqueness of the parent vertex.
* `tLen_mul_le`, `tLen_inv` --- subadditivity and inversion invariance, which
  make `d(xΔ, yΔ) = tLen φ (x⁻¹y)` a left-invariant pseudometric.
* `tLen_cyclicWord_pow` --- a cyclically reduced word of `k` syllables has
  `tLen (c ^ n) = n k`.  This is the linear orbit growth an axis needs, and it
  is `HNNTorsionFree.concatN` together with the seam condition of
  `HNNTorsionFree.CyclicWord`.
-/

namespace GroupApproximation
namespace GGT
namespace BassSerreHNN

open GroupApproximation.HNNBritton

universe u

variable {G : Type u} [Group G] {A B : Subgroup G}

/-! ## Spelling identities -/

/-- A one-syllable spelling. -/
theorem spell_singleton (φ : A ≃* B) (u : ℤˣ) (g : G) :
    spell φ [(u, g)] = HNNExtension.t ^ (u : ℤ) * HNNExtension.of g := by
  have h : spell φ [(u, g)]
      = HNNExtension.t ^ (u : ℤ) * HNNExtension.of g * spell φ [] :=
    spell_cons φ (u, g) []
  rw [h, spell_nil, mul_one]

/-- Appending one syllable on the right. -/
theorem wordProd_concat (φ : A ≃* B) (g : G) (L : List (ℤˣ × G)) (u : ℤˣ)
    (h : G) :
    wordProd φ g (L ++ [(u, h)]) =
      wordProd φ g L * (HNNExtension.t ^ (u : ℤ) * HNNExtension.of h) := by
  show HNNExtension.of g * spell φ (L ++ [(u, h)])
      = HNNExtension.of g * spell φ L *
        (HNNExtension.t ^ (u : ℤ) * HNNExtension.of h)
  rw [spell_append, spell_singleton, mul_assoc]

/-- Peeling one syllable off the left. -/
theorem wordProd_cons (φ : A ≃* B) (g : G) (u : ℤˣ) (h : G)
    (L : List (ℤˣ × G)) :
    wordProd φ g ((u, h) :: L) =
      HNNExtension.of g * HNNExtension.t ^ (u : ℤ) * wordProd φ h L := by
  have h1 : spell φ ((u, h) :: L)
      = HNNExtension.t ^ (u : ℤ) * HNNExtension.of h * spell φ L :=
    spell_cons φ (u, h) L
  show HNNExtension.of g * spell φ ((u, h) :: L)
      = HNNExtension.of g * HNNExtension.t ^ (u : ℤ) *
        (HNNExtension.of h * spell φ L)
  rw [h1, mul_assoc, mul_assoc]

/-- The length of a list with one entry appended. -/
theorem length_concat {X : Type*} (L : List X) (b : X) :
    (L ++ [b]).length = L.length + 1 := by
  rw [List.length_append]

/-! ## Signed powers of the stable letter -/

/-- The stable letter at the opposite sign. -/
theorem t_zpow_neg (φ : A ≃* B) (u : ℤˣ) :
    (HNNExtension.t : HNNExtension G A B φ) ^ ((-u : ℤˣ) : ℤ)
      = ((HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ))⁻¹ := by
  rw [Units.val_neg, zpow_neg]

/-- **The pinch identity at either sign.**  Conjugating the associated subgroup
of the sign `u` by `t ^ u` lands in the base copy.  For `u = 1` this is
`HNNBritton.t_conj_mem_range_iff`, for `u = -1` it is
`HNNBritton.t_inv_conj_mem_range_iff`. -/
theorem t_zpow_conj_mem_range (φ : A ≃* B) {u : ℤˣ} {c : G}
    (hc : c ∈ HNNExtension.toSubgroup A B u) :
    (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ) * HNNExtension.of c *
        ((HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ))⁻¹ ∈
      (HNNExtension.of : G →* HNNExtension G A B φ).range := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · have hv : (((1 : ℤˣ)) : ℤ) = 1 := rfl
    rw [hv, zpow_one]
    exact (t_conj_mem_range_iff φ c).2 hc
  · have hv : (((-1 : ℤˣ)) : ℤ) = -1 := rfl
    rw [hv, zpow_neg, zpow_one, inv_inv]
    exact (t_inv_conj_mem_range_iff φ c).2 hc

/-- Appending one syllable to a pinch-free list, when the seam is checked
against the displayed final syllable. -/
theorem noPinch_concat {L : List (ℤˣ × G)} {v : ℤˣ} {c : G} {u : ℤˣ} {h : G}
    (hL : NoPinch A B (L ++ [(v, c)]))
    (hseam : c ∈ HNNExtension.toSubgroup A B v → v = u) :
    NoPinch A B ((L ++ [(v, c)]) ++ [(u, h)]) :=
  List.IsChain.append hL (noPinch_singleton _) (by
    intro p hp q hq hmem
    rw [List.getLast?_concat, Option.mem_some_iff] at hp
    rw [List.head?_cons, Option.mem_some_iff] at hq
    subst hp
    subst hq
    exact hseam hmem)

/-! ## The length function -/

/-- The set of syllable counts of Britton-reduced spellings of `x`. -/
def reducedLengths (φ : A ≃* B) (x : HNNExtension G A B φ) : Set ℕ :=
  {n | ∃ (g : G) (l : List (ℤˣ × G)),
    NoPinch A B l ∧ wordProd φ g l = x ∧ l.length = n}

theorem reducedLengths_nonempty (φ : A ≃* B) (x : HNNExtension G A B φ) :
    (reducedLengths φ x).Nonempty := by
  obtain ⟨g, l, hl, hprod⟩ := exists_hasSpelling φ x
  exact ⟨l.length, g, l, hl, hprod, rfl⟩

/-- **The syllable length of an element of an HNN extension**: the number of
stable letters in any Britton-reduced spelling. -/
noncomputable def tLen (φ : A ≃* B) (x : HNNExtension G A B φ) : ℕ :=
  sInf (reducedLengths φ x)

theorem tLen_mem (φ : A ≃* B) (x : HNNExtension G A B φ) :
    tLen φ x ∈ reducedLengths φ x :=
  Nat.sInf_mem (reducedLengths_nonempty φ x)

/-- **Britton's Lemma as a well-definedness statement.**  Two pinch-free
spellings of the same element have the same number of syllables, because they
have the same list of signs. -/
theorem length_eq_of_noPinch (φ : A ≃* B) {x : HNNExtension G A B φ}
    {g₁ g₂ : G} {l₁ l₂ : List (ℤˣ × G)}
    (h₁ : NoPinch A B l₁) (hp₁ : wordProd φ g₁ l₁ = x)
    (h₂ : NoPinch A B l₂) (hp₂ : wordProd φ g₂ l₂ = x) :
    l₁.length = l₂.length := by
  have hprod : (toReducedWord h₁ g₁).prod φ = (toReducedWord h₂ g₂).prod φ := by
    rw [toReducedWord_prod, toReducedWord_prod, hp₁, hp₂]
  have hmap :=
    (HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq φ hprod).1
  simpa using congrArg List.length hmap

/-- **Every pinch-free spelling computes the length.** -/
theorem tLen_eq (φ : A ≃* B) {x : HNNExtension G A B φ} {g : G}
    {l : List (ℤˣ × G)} (hl : NoPinch A B l) (hp : wordProd φ g l = x) :
    tLen φ x = l.length := by
  obtain ⟨g', l', hl', hp', hlen⟩ := tLen_mem φ x
  rw [← hlen]
  exact length_eq_of_noPinch φ hl' hp' hl hp

@[simp] theorem tLen_of (φ : A ≃* B) (g : G) :
    tLen φ (HNNExtension.of g : HNNExtension G A B φ) = 0 := by
  have h := tLen_eq φ (l := ([] : List (ℤˣ × G))) noPinch_nil (wordProd_nil φ g)
  simpa using h

@[simp] theorem tLen_one (φ : A ≃* B) :
    tLen φ (1 : HNNExtension G A B φ) = 0 := by
  have h := tLen_of φ (1 : G)
  rwa [map_one] at h

/-- **Britton's Lemma.**  An element has no stable letter exactly when it lies
in the base copy. -/
theorem tLen_eq_zero_iff (φ : A ≃* B) (x : HNNExtension G A B φ) :
    tLen φ x = 0 ↔ x ∈ (HNNExtension.of : G →* HNNExtension G A B φ).range := by
  constructor
  · intro h0
    obtain ⟨g, l, _, hp, hlen⟩ := tLen_mem φ x
    rw [h0] at hlen
    have hnil : l = [] := List.length_eq_zero_iff.1 hlen
    subst hnil
    refine ⟨g, ?_⟩
    rw [← hp, wordProd_nil]
  · rintro ⟨g, rfl⟩
    exact tLen_of φ g

/-! ## The calculus of `tLen` -/

theorem tLen_of_mul (φ : A ≃* B) (g : G) (x : HNNExtension G A B φ) :
    tLen φ (HNNExtension.of g * x) = tLen φ x := by
  obtain ⟨g', l, hl, hp, hlen⟩ := tLen_mem φ x
  have hp2 : wordProd φ (g * g') l = HNNExtension.of g * x := by
    calc wordProd φ (g * g') l
        = HNNExtension.of (g * g') * spell φ l := rfl
      _ = HNNExtension.of g * (HNNExtension.of g' * spell φ l) := by
            rw [map_mul, mul_assoc]
      _ = HNNExtension.of g * wordProd φ g' l := rfl
      _ = HNNExtension.of g * x := by rw [hp]
  rw [tLen_eq φ hl hp2]
  exact hlen

theorem tLen_mul_of (φ : A ≃* B) (x : HNNExtension G A B φ) (g : G) :
    tLen φ (x * HNNExtension.of g) = tLen φ x := by
  obtain ⟨g', l, hl, hp, hlen⟩ := tLen_mem φ x
  rcases eq_or_ne l [] with rfl | hne
  · have hx : x = HNNExtension.of g' := by rw [← hp, wordProd_nil]
    rw [hx, ← map_mul, tLen_of, tLen_of]
  · have hp2 : wordProd φ g' (absorbLast l g) = x * HNNExtension.of g := by
      calc wordProd φ g' (absorbLast l g)
          = HNNExtension.of g' * spell φ (absorbLast l g) := rfl
        _ = HNNExtension.of g' * (spell φ l * HNNExtension.of g) := by
              rw [spell_absorbLast φ l g hne]
        _ = HNNExtension.of g' * spell φ l * HNNExtension.of g := by
              rw [mul_assoc]
        _ = wordProd φ g' l * HNNExtension.of g := rfl
        _ = x * HNNExtension.of g := by rw [hp]
    rw [tLen_eq φ (noPinch_absorbLast l g hl) hp2, absorbLast_length l g]
    exact hlen

/-- **Crossing one edge.**  Right multiplication by a signed stable letter
raises the syllable count by at most one.  The proof is the pinch dichotomy at
the final syllable of a reduced spelling. -/
theorem tLen_mul_t_zpow_le (φ : A ≃* B) (x : HNNExtension G A B φ) (u : ℤˣ) :
    tLen φ (x * (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ))
      ≤ tLen φ x + 1 := by
  obtain ⟨g, l, hl, hp, hlen⟩ := tLen_mem φ x
  rcases List.eq_nil_or_concat' l with rfl | ⟨L, b, rfl⟩
  · have hx : x = HNNExtension.of g := by rw [← hp, wordProd_nil]
    have hp2 : wordProd φ g [(u, (1 : G))]
        = x * (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ) := by
      have h1 : wordProd φ g [(u, (1 : G))]
          = wordProd φ g [] *
            ((HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ) *
              HNNExtension.of (1 : G)) :=
        wordProd_concat φ g [] u 1
      rw [h1, wordProd_nil, map_one, mul_one, hx]
    have e1 : tLen φ (x * (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ))
        = 1 := by
      have h := tLen_eq φ (noPinch_singleton ((u : ℤˣ), (1 : G))) hp2
      simpa using h
    have e2 : tLen φ x = 0 := by rw [hx, tLen_of]
    omega
  · obtain ⟨v, c⟩ := b
    have hL : NoPinch A B L := hl.infix ⟨[], [(v, c)], by simp⟩
    by_cases hpinch : c ∈ HNNExtension.toSubgroup A B v ∧ u = -v
    · obtain ⟨hcv, rfl⟩ := hpinch
      obtain ⟨d, hd⟩ := t_zpow_conj_mem_range (φ := φ) hcv
      have hxt : x * (HNNExtension.t : HNNExtension G A B φ) ^ ((-v : ℤˣ) : ℤ)
          = wordProd φ g L * HNNExtension.of d := by
        rw [← hp, wordProd_concat, t_zpow_neg, hd, mul_assoc]
      have e1 : tLen φ (x *
            (HNNExtension.t : HNNExtension G A B φ) ^ ((-v : ℤˣ) : ℤ))
          = L.length := by
        rw [hxt, tLen_mul_of, tLen_eq φ hL rfl]
      have e2 : tLen φ x = L.length + 1 := by
        rw [← hlen, length_concat]
      omega
    · have hnew : NoPinch A B ((L ++ [(v, c)]) ++ [(u, (1 : G))]) := by
        refine noPinch_concat hl ?_
        intro hmem
        by_contra hne
        have hvu : v = -u := Int.units_ne_iff_eq_neg.1 hne
        have huv : u = -v := by rw [hvu, neg_neg]
        exact hpinch ⟨hmem, huv⟩
      have hp2 : wordProd φ g ((L ++ [(v, c)]) ++ [(u, (1 : G))])
          = x * (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ) := by
        rw [wordProd_concat, hp, map_one, mul_one]
      have e1 : tLen φ (x * (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ))
          = L.length + 1 + 1 := by
        rw [tLen_eq φ hnew hp2, length_concat, length_concat]
      have e2 : tLen φ x = L.length + 1 := by
        rw [← hlen, length_concat]
      omega

/-- Subadditivity against an arbitrary spelling: no reducedness is needed for
an upper bound. -/
theorem tLen_mul_wordProd_le (φ : A ≃* B) :
    ∀ (l : List (ℤˣ × G)) (x : HNNExtension G A B φ) (g : G),
      tLen φ (x * wordProd φ g l) ≤ tLen φ x + l.length := by
  intro l
  induction l with
  | nil =>
      intro x g
      rw [wordProd_nil, tLen_mul_of]
      simp
  | cons b L ih =>
      intro x g
      obtain ⟨u, h⟩ := b
      have hkey : x * wordProd φ g ((u, h) :: L)
          = (x * HNNExtension.of g *
              (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ)) *
            wordProd φ h L := by
        rw [wordProd_cons]
        simp only [mul_assoc]
      have h1 : tLen φ (x * HNNExtension.of g *
            (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ))
          ≤ tLen φ x + 1 := by
        have h2 := tLen_mul_t_zpow_le φ (x * HNNExtension.of g) u
        rwa [tLen_mul_of] at h2
      have h3 := ih (x * HNNExtension.of g *
        (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ)) h
      rw [hkey]
      simp only [List.length_cons]
      omega

/-- **Subadditivity.** -/
theorem tLen_mul_le (φ : A ≃* B) (x y : HNNExtension G A B φ) :
    tLen φ (x * y) ≤ tLen φ x + tLen φ y := by
  obtain ⟨g, l, _, hp, hlen⟩ := tLen_mem φ y
  have h := tLen_mul_wordProd_le φ l x g
  rw [hp, hlen] at h
  exact h

@[simp] theorem tLen_t (φ : A ≃* B) :
    tLen φ (HNNExtension.t : HNNExtension G A B φ) = 1 := by
  have h1 : wordProd φ (1 : G) [((1 : ℤˣ), (1 : G))]
      = wordProd φ (1 : G) ([] : List (ℤˣ × G)) *
        ((HNNExtension.t : HNNExtension G A B φ) ^ (((1 : ℤˣ)) : ℤ) *
          HNNExtension.of (1 : G)) :=
    wordProd_concat φ (1 : G) ([] : List (ℤˣ × G)) (1 : ℤˣ) (1 : G)
  have hv : (((1 : ℤˣ)) : ℤ) = 1 := rfl
  have hp : wordProd φ (1 : G) [((1 : ℤˣ), (1 : G))]
      = (HNNExtension.t : HNNExtension G A B φ) := by
    rw [h1, wordProd_nil, hv, zpow_one, map_one, one_mul, mul_one]
  have h := tLen_eq φ (noPinch_singleton ((1 : ℤˣ), (1 : G))) hp
  simpa using h

/-- The bounded-induction half of inversion invariance. -/
theorem tLen_inv_le (φ : A ≃* B) :
    ∀ (n : ℕ) (x : HNNExtension G A B φ), tLen φ x ≤ n → tLen φ x⁻¹ ≤ n := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have h0 : tLen φ x = 0 := Nat.le_zero.1 hx
      obtain ⟨g, hg⟩ := (tLen_eq_zero_iff φ x).1 h0
      rw [← hg, ← map_inv, tLen_of]
  | succ n ih =>
      intro x hx
      obtain ⟨g, l, hl, hp, hlen⟩ := tLen_mem φ x
      rcases l with _ | ⟨b, L⟩
      · have h0 : tLen φ x = 0 := hlen.symm
        obtain ⟨g', hg'⟩ := (tLen_eq_zero_iff φ x).1 h0
        rw [← hg', ← map_inv, tLen_of]
        omega
      · obtain ⟨u, h⟩ := b
        have hLchain : NoPinch A B L := hl.tail
        have hyLen : tLen φ (wordProd φ h L) = L.length :=
          tLen_eq φ hLchain rfl
        have hcons : ((u, h) :: L).length = L.length + 1 := rfl
        have hyle : tLen φ (wordProd φ h L) ≤ n := by
          rw [hyLen]
          rw [hcons] at hlen
          omega
        have hyinv : tLen φ (wordProd φ h L)⁻¹ ≤ n := ih _ hyle
        have hxeq : x = HNNExtension.of g *
            (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ) *
            wordProd φ h L := by
          rw [← hp, wordProd_cons]
        have hinv : x⁻¹ = (wordProd φ h L)⁻¹ *
            (HNNExtension.t : HNNExtension G A B φ) ^ ((-u : ℤˣ) : ℤ) *
            HNNExtension.of g⁻¹ := by
          rw [hxeq, t_zpow_neg, map_inv]
          group
        rw [hinv, tLen_mul_of]
        refine le_trans (tLen_mul_t_zpow_le φ (wordProd φ h L)⁻¹ (-u)) ?_
        omega

/-- **Inversion invariance.**  With `tLen_of_mul` and `tLen_mul_of` this is
what makes `tLen φ (x⁻¹ y)` a symmetric, left-invariant distance on the coset
space. -/
theorem tLen_inv (φ : A ≃* B) (x : HNNExtension G A B φ) :
    tLen φ x⁻¹ = tLen φ x := by
  refine le_antisymm (tLen_inv_le φ (tLen φ x) x le_rfl) ?_
  have h := tLen_inv_le φ (tLen φ x⁻¹) x⁻¹ le_rfl
  rwa [inv_inv] at h

/-- The syllable length of a conjugate of a base element is the length of the
element it conjugates. -/
theorem tLen_of_mul_of (φ : A ≃* B) (a : G) (z : HNNExtension G A B φ)
    (b : G) :
    tLen φ (HNNExtension.of a * z * HNNExtension.of b) = tLen φ z := by
  rw [tLen_mul_of, tLen_of_mul]

/-! ## Powers of a cyclically reduced word -/

@[simp] theorem concatN_zero {X : Type*} (L : List X) :
    HNNTorsionFree.concatN 0 L = [] := rfl

@[simp] theorem concatN_succ {X : Type*} (n : ℕ) (L : List X) :
    HNNTorsionFree.concatN (n + 1) L = L ++ HNNTorsionFree.concatN n L := rfl

theorem concatN_length {X : Type*} (n : ℕ) (L : List X) :
    (HNNTorsionFree.concatN n L).length = n * L.length := by
  induction n with
  | zero => simp
  | succ m ih =>
      simp only [concatN_succ, List.length_append, ih, Nat.succ_mul]
      omega

theorem concatN_ne_nil {X : Type*} {L : List X} (hL : L ≠ []) {n : ℕ}
    (hn : n ≠ 0) : HNNTorsionFree.concatN n L ≠ [] := by
  cases n with
  | zero => exact absurd rfl hn
  | succ m =>
      rw [concatN_succ]
      cases L with
      | nil => exact absurd rfl hL
      | cons a l => simp

theorem head?_concatN_succ {X : Type*} {L : List X} (hL : L ≠ []) (n : ℕ) :
    (HNNTorsionFree.concatN (n + 1) L).head? = L.head? := by
  cases L with
  | nil => exact absurd rfl hL
  | cons a l => simp

theorem spell_concatN (φ : A ≃* B) (n : ℕ) (L : List (ℤˣ × G)) :
    spell φ (HNNTorsionFree.concatN n L) = (spell φ L) ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [concatN_succ, spell_append, ih, pow_succ']

/-- **The seam condition keeps every power reduced.** -/
theorem noPinch_concatN (c : HNNTorsionFree.CyclicWord G A B) (n : ℕ) :
    NoPinch A B (HNNTorsionFree.concatN n c.letters) := by
  induction n with
  | zero => exact noPinch_nil
  | succ m ih =>
      rw [concatN_succ]
      refine List.IsChain.append c.chain ih ?_
      intro p hp q hq
      cases m with
      | zero => simp at hq
      | succ k =>
          rw [head?_concatN_succ c.nonempty k] at hq
          exact c.cyclic p hp q hq

/-- **Linear growth along an axis.**  A cyclically reduced word with `k`
syllables has `tLen (c ^ n) = n k`: its `n`-th power is spelled by the `n`-fold
concatenation of its letter list, which the seam condition keeps pinch-free. -/
theorem tLen_cyclicWord_pow (φ : A ≃* B) (c : HNNTorsionFree.CyclicWord G A B)
    (n : ℕ) :
    tLen φ (c.elem φ ^ n) = n * c.letters.length := by
  have hprod : wordProd φ (1 : G) (HNNTorsionFree.concatN n c.letters)
      = c.elem φ ^ n := by
    rw [wordProd_one, spell_concatN]
    rfl
  rw [tLen_eq φ (noPinch_concatN c n) hprod, concatN_length]

theorem tLen_cyclicWord (φ : A ≃* B) (c : HNNTorsionFree.CyclicWord G A B) :
    tLen φ (c.elem φ) = c.letters.length := by
  have h := tLen_cyclicWord_pow φ c 1
  rwa [pow_one, one_mul] at h

theorem tLen_cyclicWord_pos (φ : A ≃* B)
    (c : HNNTorsionFree.CyclicWord G A B) : 0 < tLen φ (c.elem φ) := by
  rw [tLen_cyclicWord]
  exact List.length_pos_iff.2 c.nonempty

end BassSerreHNN
end GGT
end GroupApproximation
