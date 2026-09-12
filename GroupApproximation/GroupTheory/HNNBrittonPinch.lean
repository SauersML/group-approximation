import Mathlib.GroupTheory.HNNExtension
import Mathlib.Tactic.Group

/-!
# Britton's Lemma in pinch form

Mathlib already certifies Britton's Lemma for a single-stable-letter HNN
extension, as `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`:
a Britton-reduced word whose product lands in the base copy carries no
stable letter at all.  What Mathlib does *not* provide is the shape in
which the classical applications consume the lemma — the Novikov--Boone
construction, and hence the Adian--Rabin corollary quoted at
the companion notes' undecidability section,
argue about an explicit alternating product

  `g₀ · t^{e₁} g₁ · t^{e₂} g₂ ⋯ t^{eₙ} gₙ`

presented as a literal list of syllables, and use the *pinch dichotomy*:
a word that collapses into the base must contain a pinch.

This module supplies that layer, entirely on top of Mathlib's theorem.

* `spell`, `wordProd` — the element of the extension spelled by a head
  and a list of syllables `(sign, base element)`.
* `NoPinch` — the Britton reducedness condition, definitionally the
  `chain` field of `HNNExtension.NormalWord.ReducedWord`, with the
  constructors and destructors one needs to build and take apart words.
* `wordProd_notMem_range`, `wordProd_ne_one` — **Britton's Lemma**: a
  pinch-free word with at least one stable letter is not in the base
  copy, hence is not `1`.
* `exists_pinch_of_mem_range` — the contrapositive with an explicit
  index: a word collapsing into the base has a position `i` at which the
  syllable lies in the associated subgroup of its own sign while the
  next sign differs, i.e. a literal pinch `t^{u} g t^{-u}`.
* `t_conj_mem_range_iff`, `t_inv_conj_mem_range_iff` — the two
  single-letter conjugation criteria, which are the form actually used
  when checking Boone-style relations: `t g t⁻¹` lies in the base
  exactly for `g ∈ A`, and `t⁻¹ g t` exactly for `g ∈ B`, with the
  values `φ g` and `φ⁻¹ g`.
* `exponentSum`, `t_zpow_notMem_range`, `t_zpow_ne_one` — the stable
  letter has infinite order and no nonzero power meets the base.

## Orientation warning

Mathlib's convention is `t * a * t⁻¹ = φ a` for `a ∈ A`
(`HNNExtension.equiv_eq_conj`), so `HNNExtension.toSubgroup A B 1 = A`
and `HNNExtension.toSubgroup A B (-1) = B`, and a *pinch* is a subword
`t g t⁻¹` with `g ∈ A` or `t⁻¹ g t` with `g ∈ B`.  Many textbook
treatments (Lyndon--Schupp, Rotman) use `t⁻¹ a t = φ a` instead, which
swaps the two roles.  Everything below follows Mathlib.

## What is *not* here

Britton's Lemma for **several stable letters** — syllables in a common
base `G`, each letter `tᵢ` carrying its own associated pair
`(Aᵢ, Bᵢ, φᵢ)` — is not in Mathlib (`GroupTheory/HNNExtension.lean` is the
only Mathlib file mentioning HNN extensions at all, and it is
single-letter) and is not proved here.  It is not a corollary of the
single-letter statement applied once: there is no homomorphism collapsing
the other letters, since killing `tⱼ` would force `a = φⱼ a` on `Aⱼ`.  The
classical route is induction on the number of letters over the *iterated*
extension, whose inductive hypothesis at each syllable is exactly the
strong form `wordProd_notMem_range` proved below — a syllable that itself
contains a stable letter is outside the base copy, hence outside `Aᵢ` and
`Bᵢ`, so it cannot pinch.  Building that tower needs
`Subgroup.equivMapOfInjective` to transport each associated pair up one
level along `HNNExtension.of`.

The good-subgroup form of the lemma, the other thing a
machine-to-group construction consumes, is in `HNNBrittonSpelling`.
-/

namespace GroupApproximation
namespace HNNBritton

universe u

variable {G : Type u} [Group G] {A B : Subgroup G}

/-! ## Syllable lists and their spellings -/

/-- The element of the HNN extension spelled by a list of syllables: the
`i`-th syllable `(uᵢ, gᵢ)` contributes `t^{uᵢ} · gᵢ`. -/
def spell (φ : A ≃* B) (l : List (ℤˣ × G)) : HNNExtension G A B φ :=
  (l.map fun x => HNNExtension.t ^ (x.1 : ℤ) * HNNExtension.of x.2).prod

@[simp] theorem spell_nil (φ : A ≃* B) : spell φ ([] : List (ℤˣ × G)) = 1 := rfl

@[simp] theorem spell_cons (φ : A ≃* B) (x : ℤˣ × G) (l : List (ℤˣ × G)) :
    spell φ (x :: l) =
      HNNExtension.t ^ (x.1 : ℤ) * HNNExtension.of x.2 * spell φ l := by
  simp [spell]

theorem spell_append (φ : A ≃* B) (l₁ l₂ : List (ℤˣ × G)) :
    spell φ (l₁ ++ l₂) = spell φ l₁ * spell φ l₂ := by
  simp [spell, List.map_append, List.prod_append]

/-- A positive stable letter at the head of a spelling. -/
theorem spell_cons_one (φ : A ≃* B) (g : G) (l : List (ℤˣ × G)) :
    spell φ (((1 : ℤˣ), g) :: l) =
      HNNExtension.t * HNNExtension.of g * spell φ l := by
  have hv : (((1 : ℤˣ) : ℤ)) = 1 := rfl
  simp only [spell_cons, hv]
  group

/-- A negative stable letter at the head of a spelling. -/
theorem spell_cons_neg_one (φ : A ≃* B) (g : G) (l : List (ℤˣ × G)) :
    spell φ (((-1 : ℤˣ), g) :: l) =
      HNNExtension.t⁻¹ * HNNExtension.of g * spell φ l := by
  have hv : (((-1 : ℤˣ) : ℤ)) = -1 := rfl
  simp only [spell_cons, hv]
  group

/-- The element spelled by a head `g` followed by a list of syllables:
`g · t^{u₁} g₁ ⋯ t^{uₙ} gₙ`.  This is definitionally
`HNNExtension.NormalWord.ReducedWord.prod`. -/
def wordProd (φ : A ≃* B) (g : G) (l : List (ℤˣ × G)) : HNNExtension G A B φ :=
  HNNExtension.of g * spell φ l

@[simp] theorem wordProd_nil (φ : A ≃* B) (g : G) :
    wordProd φ g ([] : List (ℤˣ × G)) = HNNExtension.of g := by
  simp [wordProd]

theorem wordProd_one (φ : A ≃* B) (l : List (ℤˣ × G)) :
    wordProd φ 1 l = spell φ l := by
  simp [wordProd]

/-! ## The pinch condition -/

/-- **Britton reducedness.**  A syllable list has no pinch when no
syllable that lies in the associated subgroup of its own sign is
followed by the opposite sign; that is, the word contains no subword
`t^{u} g t^{-u}` with `g ∈ HNNExtension.toSubgroup A B u`.

This is definitionally the `chain` field of
`HNNExtension.NormalWord.ReducedWord`. -/
def NoPinch (A B : Subgroup G) (l : List (ℤˣ × G)) : Prop :=
  List.IsChain
    (fun a b : ℤˣ × G =>
      a.2 ∈ HNNExtension.toSubgroup A B a.1 → a.1 = b.1) l

theorem noPinch_nil : NoPinch A B ([] : List (ℤˣ × G)) := List.isChain_nil

theorem noPinch_singleton (x : ℤˣ × G) : NoPinch A B [x] :=
  List.isChain_singleton x

/-- Extend a pinch-free list on the left: only the seam with the current
head has to be checked. -/
theorem noPinch_cons {x : ℤˣ × G} {l : List (ℤˣ × G)}
    (hseam : ∀ y ∈ l.head?,
      x.2 ∈ HNNExtension.toSubgroup A B x.1 → x.1 = y.1)
    (hl : NoPinch A B l) : NoPinch A B (x :: l) :=
  List.isChain_cons.2 ⟨hseam, hl⟩

/-- Extending on the left is free when the head syllable is outside the
associated subgroup of its sign. -/
theorem noPinch_cons_of_notMem {x : ℤˣ × G} {l : List (ℤˣ × G)}
    (hx : x.2 ∉ HNNExtension.toSubgroup A B x.1) (hl : NoPinch A B l) :
    NoPinch A B (x :: l) :=
  noPinch_cons (fun _ _ hmem => absurd hmem hx) hl

/-- Extending on the left is free when the head syllable repeats the
sign that follows. -/
theorem noPinch_cons_of_sign_eq {x : ℤˣ × G} {l : List (ℤˣ × G)}
    (hx : ∀ y ∈ l.head?, x.1 = y.1) (hl : NoPinch A B l) :
    NoPinch A B (x :: l) :=
  noPinch_cons (fun y hy _ => hx y hy) hl

/-- Extend a pinch-free list on the left when the next syllable is
displayed explicitly: only the single seam relation has to be checked. -/
theorem noPinch_cons_cons {x y : ℤˣ × G} {l : List (ℤˣ × G)}
    (hseam : x.2 ∈ HNNExtension.toSubgroup A B x.1 → x.1 = y.1)
    (hl : NoPinch A B (y :: l)) : NoPinch A B (x :: y :: l) :=
  List.isChain_cons_cons.2 ⟨hseam, hl⟩

theorem NoPinch.tail {x : ℤˣ × G} {l : List (ℤˣ × G)}
    (h : NoPinch A B (x :: l)) : NoPinch A B l :=
  (List.isChain_cons.1 h).2

theorem NoPinch.seam {x : ℤˣ × G} {l : List (ℤˣ × G)}
    (h : NoPinch A B (x :: l)) :
    ∀ y ∈ l.head?, x.2 ∈ HNNExtension.toSubgroup A B x.1 → x.1 = y.1 :=
  (List.isChain_cons.1 h).1

/-- Pinch-freeness passes to infixes. -/
theorem NoPinch.infix {l l' : List (ℤˣ × G)} (h : NoPinch A B l)
    (hinf : l' <:+: l) : NoPinch A B l' :=
  List.IsChain.infix h hinf

/-! ## The bridge to Mathlib's reduced words -/

/-- A pinch-free syllable list with a head, packaged as the reduced word
Mathlib's Britton lemma consumes. -/
def toReducedWord {l : List (ℤˣ × G)} (h : NoPinch A B l) (g : G) :
    HNNExtension.NormalWord.ReducedWord G A B where
  head := g
  toList := l
  chain := h

@[simp] theorem toReducedWord_toList {l : List (ℤˣ × G)} (h : NoPinch A B l)
    (g : G) : (toReducedWord h g).toList = l := rfl

@[simp] theorem toReducedWord_head {l : List (ℤˣ × G)} (h : NoPinch A B l)
    (g : G) : (toReducedWord h g).head = g := rfl

@[simp] theorem toReducedWord_prod (φ : A ≃* B) {l : List (ℤˣ × G)}
    (h : NoPinch A B l) (g : G) :
    (toReducedWord h g).prod φ = wordProd φ g l := rfl

/-! ## Britton's Lemma -/

/-- **Britton's Lemma.**  A pinch-free word carrying at least one stable
letter does not lie in the base copy.

This is `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range` read
through the syllable-list interface. -/
theorem wordProd_notMem_range (φ : A ≃* B) {g : G} {l : List (ℤˣ × G)}
    (hl : l ≠ []) (h : NoPinch A B l) :
    wordProd φ g l ∉
      (HNNExtension.of : G →* HNNExtension G A B φ).range := by
  intro hmem
  refine hl ?_
  have h0 : (toReducedWord h g).prod φ ∈
      (HNNExtension.of : G →* HNNExtension G A B φ).range := by
    rw [toReducedWord_prod]
    exact hmem
  simpa using
    HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ
      (toReducedWord h g) h0

/-- **Britton's Lemma, nontriviality form.**  A pinch-free word carrying
at least one stable letter is not the identity. -/
theorem wordProd_ne_one (φ : A ≃* B) {g : G} {l : List (ℤˣ × G)}
    (hl : l ≠ []) (h : NoPinch A B l) : wordProd φ g l ≠ 1 := by
  intro h1
  refine wordProd_notMem_range (g := g) φ hl h ?_
  rw [h1]
  exact ⟨1, map_one _⟩

/-- Britton's Lemma for a headless spelling. -/
theorem spell_ne_one (φ : A ≃* B) {l : List (ℤˣ × G)} (hl : l ≠ [])
    (h : NoPinch A B l) : spell φ l ≠ 1 := by
  have h0 := wordProd_ne_one (g := 1) φ hl h
  rwa [wordProd_one] at h0

/-- For a pinch-free word, membership in the base copy is *equivalent* to
carrying no stable letter. -/
theorem wordProd_mem_range_iff (φ : A ≃* B) {g : G} {l : List (ℤˣ × G)}
    (h : NoPinch A B l) :
    wordProd φ g l ∈
        (HNNExtension.of : G →* HNNExtension G A B φ).range ↔ l = [] := by
  constructor
  · intro hmem
    by_contra hl
    exact wordProd_notMem_range φ hl h hmem
  · rintro rfl
    exact ⟨g, by simp⟩

/-- **The pinch dichotomy.**  A word that collapses into the base copy is
not pinch-free. -/
theorem not_noPinch_of_mem_range (φ : A ≃* B) {g : G} {l : List (ℤˣ × G)}
    (hl : l ≠ [])
    (hmem : wordProd φ g l ∈
      (HNNExtension.of : G →* HNNExtension G A B φ).range) :
    ¬ NoPinch A B l :=
  fun h => wordProd_notMem_range φ hl h hmem

/-- **The pinch dichotomy with a witness.**  A word that collapses into
the base copy contains a literal pinch: a position `i` whose syllable
lies in the associated subgroup of its own sign and whose successor
carries the opposite sign, i.e. a subword `t^{u} gᵢ t^{-u}` with
`gᵢ ∈ HNNExtension.toSubgroup A B u`. -/
theorem exists_pinch_of_mem_range (φ : A ≃* B) {g : G} {l : List (ℤˣ × G)}
    (hl : l ≠ [])
    (hmem : wordProd φ g l ∈
      (HNNExtension.of : G →* HNNExtension G A B φ).range) :
    ∃ (i : ℕ) (hi : i + 1 < l.length),
      (l[i]'(by omega)).2 ∈
          HNNExtension.toSubgroup A B (l[i]'(by omega)).1 ∧
        (l[i]'(by omega)).1 ≠ (l[i + 1]'hi).1 := by
  by_contra hcon
  push Not at hcon
  refine not_noPinch_of_mem_range φ hl hmem ?_
  show List.IsChain _ l
  refine List.isChain_iff_getElem.2 ?_
  intro i hi hmemA
  exact hcon i hi hmemA

/-! ## The two single-letter conjugation criteria

Mathlib already supplies `HNNExtension.toSubgroup_one : toSubgroup A B 1 = A`
and `HNNExtension.toSubgroup_neg_one : toSubgroup A B (-1) = B`, both by
`rfl`, so the pinch conditions at the two signs are definitionally
membership in `A` and in `B`. -/

/-- Conjugating an element of `A` by the stable letter lands it in the
base copy, at its `φ`-image.  This is `HNNExtension.equiv_eq_conj`
oriented for use. -/
theorem t_conj_of_mem (φ : A ≃* B) {g : G} (hg : g ∈ A) :
    (HNNExtension.t : HNNExtension G A B φ) * HNNExtension.of g *
        HNNExtension.t⁻¹ =
      HNNExtension.of ((φ ⟨g, hg⟩ : B) : G) :=
  (HNNExtension.equiv_eq_conj (φ := φ) ⟨g, hg⟩).symm

/-- Conjugating an element of `B` by the inverse stable letter lands it in
the base copy, at its `φ⁻¹`-image. -/
theorem t_inv_conj_of_mem (φ : A ≃* B) {g : G} (hg : g ∈ B) :
    (HNNExtension.t : HNNExtension G A B φ)⁻¹ * HNNExtension.of g *
        HNNExtension.t =
      HNNExtension.of ((φ.symm ⟨g, hg⟩ : A) : G) :=
  (HNNExtension.equiv_symm_eq_conj (φ := φ) ⟨g, hg⟩).symm

/-- The two-syllable spelling of `t g t⁻¹`. -/
theorem wordProd_conj (φ : A ≃* B) (g : G) :
    wordProd φ 1 [((1 : ℤˣ), g), ((-1 : ℤˣ), (1 : G))] =
      (HNNExtension.t : HNNExtension G A B φ) * HNNExtension.of g *
        HNNExtension.t⁻¹ := by
  simp only [wordProd, spell_cons_one, spell_cons_neg_one, spell_nil, map_one]
  group

/-- The two-syllable spelling of `t⁻¹ g t`. -/
theorem wordProd_conj_inv (φ : A ≃* B) (g : G) :
    wordProd φ 1 [((-1 : ℤˣ), g), ((1 : ℤˣ), (1 : G))] =
      (HNNExtension.t : HNNExtension G A B φ)⁻¹ * HNNExtension.of g *
        HNNExtension.t := by
  simp only [wordProd, spell_cons_one, spell_cons_neg_one, spell_nil, map_one]
  group

/-- **The `+1` pinch criterion.**  `t g t⁻¹` lies in the base copy exactly
when `g` lies in the unmoved associated subgroup. -/
theorem t_conj_mem_range_iff (φ : A ≃* B) (g : G) :
    ((HNNExtension.t : HNNExtension G A B φ) * HNNExtension.of g *
        HNNExtension.t⁻¹) ∈
        (HNNExtension.of : G →* HNNExtension G A B φ).range ↔ g ∈ A := by
  constructor
  · intro hmem
    by_contra hg
    have hchain : NoPinch A B [((1 : ℤˣ), g), ((-1 : ℤˣ), (1 : G))] :=
      noPinch_cons_of_notMem (x := ((1 : ℤˣ), g)) hg
        (noPinch_singleton _)
    refine wordProd_notMem_range (g := 1) φ (by simp) hchain ?_
    rw [wordProd_conj]
    exact hmem
  · intro hg
    exact ⟨_, (t_conj_of_mem φ hg).symm⟩

/-- **The `-1` pinch criterion.**  `t⁻¹ g t` lies in the base copy exactly
when `g` lies in the moved associated subgroup. -/
theorem t_inv_conj_mem_range_iff (φ : A ≃* B) (g : G) :
    ((HNNExtension.t : HNNExtension G A B φ)⁻¹ * HNNExtension.of g *
        HNNExtension.t) ∈
        (HNNExtension.of : G →* HNNExtension G A B φ).range ↔ g ∈ B := by
  constructor
  · intro hmem
    by_contra hg
    have hchain : NoPinch A B [((-1 : ℤˣ), g), ((1 : ℤˣ), (1 : G))] :=
      noPinch_cons_of_notMem (x := ((-1 : ℤˣ), g)) hg
        (noPinch_singleton _)
    refine wordProd_notMem_range (g := 1) φ (by simp) hchain ?_
    rw [wordProd_conj_inv]
    exact hmem
  · intro hg
    exact ⟨_, (t_inv_conj_of_mem φ hg).symm⟩

/-- The `+1` criterion in negative form, the shape used when checking that
a Boone-style relation cannot fire. -/
theorem t_conj_notMem_range (φ : A ≃* B) {g : G} (hg : g ∉ A) :
    ((HNNExtension.t : HNNExtension G A B φ) * HNNExtension.of g *
        HNNExtension.t⁻¹) ∉
      (HNNExtension.of : G →* HNNExtension G A B φ).range :=
  fun hmem => hg ((t_conj_mem_range_iff φ g).1 hmem)

/-- The `-1` criterion in negative form. -/
theorem t_inv_conj_notMem_range (φ : A ≃* B) {g : G} (hg : g ∉ B) :
    ((HNNExtension.t : HNNExtension G A B φ)⁻¹ * HNNExtension.of g *
        HNNExtension.t) ∉
      (HNNExtension.of : G →* HNNExtension G A B φ).range :=
  fun hmem => hg ((t_inv_conj_mem_range_iff φ g).1 hmem)

/-! ## The stable-letter exponent sum -/

/-- The homomorphism counting stable letters with sign. -/
def exponentSum (φ : A ≃* B) : HNNExtension G A B φ →* Multiplicative ℤ :=
  HNNExtension.lift 1 (Multiplicative.ofAdd 1) (fun _ => by simp)

@[simp] theorem exponentSum_of (φ : A ≃* B) (g : G) :
    exponentSum φ (HNNExtension.of g) = 1 := by
  simp [exponentSum, HNNExtension.lift_of]

@[simp] theorem exponentSum_t (φ : A ≃* B) :
    exponentSum φ (HNNExtension.t : HNNExtension G A B φ) =
      Multiplicative.ofAdd 1 := by
  simp [exponentSum, HNNExtension.lift_t]

/-- No nonzero power of the stable letter meets the base copy. -/
theorem t_zpow_notMem_range (φ : A ≃* B) {n : ℤ} (hn : n ≠ 0) :
    ((HNNExtension.t : HNNExtension G A B φ) ^ n) ∉
      (HNNExtension.of : G →* HNNExtension G A B φ).range := by
  rintro ⟨g, hg⟩
  have h1 : exponentSum φ ((HNNExtension.t : HNNExtension G A B φ) ^ n) =
      exponentSum φ (HNNExtension.of g) := by rw [hg]
  rw [map_zpow, exponentSum_t, exponentSum_of] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  simp only [toAdd_zpow, toAdd_ofAdd, toAdd_one, zsmul_eq_mul, Int.cast_id,
    mul_one] at h2
  exact hn h2

/-- **The stable letter has infinite order.** -/
theorem t_zpow_ne_one (φ : A ≃* B) {n : ℤ} (hn : n ≠ 0) :
    ((HNNExtension.t : HNNExtension G A B φ) ^ n) ≠ 1 := by
  intro h
  refine t_zpow_notMem_range φ hn ?_
  rw [h]
  exact ⟨1, map_one _⟩

end HNNBritton
end GroupApproximation
