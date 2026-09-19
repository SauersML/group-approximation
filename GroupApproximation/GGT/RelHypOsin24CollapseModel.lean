import GroupApproximation.GGT.RelHypOsinTheorem24Refuted

/-!
# A relative length function that is exact on both factors and collapses commutators

This module builds the model in which `GGT/RelHypOsin24Collapse.lean` refutes the
*third* generation of the weighted leaves, the one whose length floor `rho` is
chosen after the length function and before the relator family.

## Why a new model is needed at all

`OsinWeightedMetric.RelativeLength` has five clauses: `len 1 = 0`, only the
identity is empty, subadditivity, inversion invariance, and the peripheral
clause `len (of x) ≤ 1` for `x` in the source factor.  Nothing in that list
says the length function is the word metric of a **finite** relative generating
set `X ∪ U`, and nothing says the ambient group is hyperbolic relative to the
peripheral family.  Osin's Theorem 2.4 assumes both.

The construction below exploits exactly that.  Fix an abelian group `A` and a
homomorphism `ab : U * H →* A` -- here `A = ℤ × ℤ` and `ab` is the pair of
abelianisation coordinates -- fix a subadditive symmetric norm on `A`, and set

    len g = max (indicator of `g ≠ 1`) (norm of `ab g`).

The five clauses hold; the first summand supplies "only the identity is empty"
and the second is where all the length lives.  The resulting function is exact
on each factor: a partner element `t^k` has length `|k|`, and a source element
has length `1`.  But it is `1` on the whole commutator subgroup of the free
product, because `A` is abelian.

## The indicator is a word metric, not an ad hoc case split

The indicator is `WordMetric.wordNorm Set.univ`, packaged by
`OsinWeightedMetric.ofSymmetricGeneratingSet`: the word norm of the alphabet
`Set.univ` is `0` at the identity and `1` everywhere else, and it carries the
four length laws already.  So no decidability instance and no case split enters
the definition of `L`.

## What is proved here

`L` is a `RelativeLength Fam` (`L`), it has geodesic spellings
(`hasGeodesicSpellings_L`), and the two computations the refutation needs:
`abNorm_ab_le_one_iff_len_le_one` (an element is a letter exactly when its
abelianisation is short) and the values of `L` on the partner's generator and
its powers.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open GroupApproximation.OsinWeightedMetric

namespace Osin24Collapse

/-! ## 1.  The two-factor family: `ℤ * ℤ` -/

/-- The peripheral factor and the partner factor are both `ℤ`, written
multiplicatively.  Nothing in `OsinTheorem24Final` restricts either factor. -/
def Fam : Bool → Type
  | false => Multiplicative ℤ
  | true => Multiplicative ℤ

instance instFamGroup : ∀ b, Group (Fam b)
  | false => inferInstanceAs (Group (Multiplicative ℤ))
  | true => inferInstanceAs (Group (Multiplicative ℤ))

/-! ## 2.  The abelianisation `ℤ * ℤ →* ℤ × ℤ` -/

/-- The source coordinate, `n ↦ (n, 0)`, multiplicatively.  Written with an
explicit pair rather than a scalar multiple so that no `SMul` lemma is needed
anywhere below. -/
def srcHom : Multiplicative ℤ →* Multiplicative (ℤ × ℤ) where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x, (0 : ℤ))
  map_one' := by
    show Multiplicative.ofAdd
        (Multiplicative.toAdd (1 : Multiplicative ℤ), (0 : ℤ)) = 1
    rw [toAdd_one, Prod.mk_zero_zero, ofAdd_zero]
  map_mul' x y := by
    show Multiplicative.ofAdd (Multiplicative.toAdd (x * y), (0 : ℤ))
      = Multiplicative.ofAdd (Multiplicative.toAdd x, (0 : ℤ)) *
        Multiplicative.ofAdd (Multiplicative.toAdd y, (0 : ℤ))
    rw [toAdd_mul, ← ofAdd_add, Prod.mk_add_mk, add_zero]

/-- The partner coordinate, `n ↦ (0, n)`. -/
def parHom : Multiplicative ℤ →* Multiplicative (ℤ × ℤ) where
  toFun x := Multiplicative.ofAdd ((0 : ℤ), Multiplicative.toAdd x)
  map_one' := by
    show Multiplicative.ofAdd
        ((0 : ℤ), Multiplicative.toAdd (1 : Multiplicative ℤ)) = 1
    rw [toAdd_one, Prod.mk_zero_zero, ofAdd_zero]
  map_mul' x y := by
    show Multiplicative.ofAdd ((0 : ℤ), Multiplicative.toAdd (x * y))
      = Multiplicative.ofAdd ((0 : ℤ), Multiplicative.toAdd x) *
        Multiplicative.ofAdd ((0 : ℤ), Multiplicative.toAdd y)
    rw [toAdd_mul, ← ofAdd_add, Prod.mk_add_mk, add_zero]

@[simp] theorem srcHom_apply (x : Multiplicative ℤ) :
    srcHom x = Multiplicative.ofAdd (Multiplicative.toAdd x, (0 : ℤ)) := rfl

@[simp] theorem parHom_apply (x : Multiplicative ℤ) :
    parHom x = Multiplicative.ofAdd ((0 : ℤ), Multiplicative.toAdd x) := rfl

/-- The two coordinates: the source factor is the first, the partner the
second. -/
def abFactor : ∀ b, Fam b →* Multiplicative (ℤ × ℤ)
  | false => srcHom
  | true => parHom

/-- The abelianisation of the free product, as a homomorphism. -/
def abHom : CoprodI Fam →* Multiplicative (ℤ × ℤ) := CoprodI.lift abFactor

/-- The abelianisation, read additively. -/
def ab (g : CoprodI Fam) : ℤ × ℤ := Multiplicative.toAdd (abHom g)

@[simp] theorem ab_one : ab 1 = 0 := by
  show Multiplicative.toAdd (abHom 1) = 0
  rw [map_one, toAdd_one]

@[simp] theorem ab_mul (g h : CoprodI Fam) : ab (g * h) = ab g + ab h := by
  show Multiplicative.toAdd (abHom (g * h))
      = Multiplicative.toAdd (abHom g) + Multiplicative.toAdd (abHom h)
  rw [map_mul, toAdd_mul]

@[simp] theorem ab_inv (g : CoprodI Fam) : ab g⁻¹ = - ab g := by
  show Multiplicative.toAdd (abHom g⁻¹) = -Multiplicative.toAdd (abHom g)
  rw [map_inv, toAdd_inv]

theorem ab_pow (g : CoprodI Fam) (n : ℕ) : ab (g ^ n) = n • ab g := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ab_mul, ih, succ_nsmul]

/-- A source element contributes to the first coordinate only. -/
theorem ab_of_source (x : Fam false) :
    ab (CoprodI.of x) = (Multiplicative.toAdd (x : Multiplicative ℤ), 0) := by
  show Multiplicative.toAdd (CoprodI.lift abFactor (CoprodI.of x)) = _
  rw [CoprodI.lift_of]
  show Multiplicative.toAdd (srcHom (x : Multiplicative ℤ)) = _
  rw [srcHom_apply, toAdd_ofAdd]
  rfl

/-- A partner element contributes to the second coordinate only. -/
theorem ab_of_partner (y : Fam true) :
    ab (CoprodI.of y) = (0, Multiplicative.toAdd (y : Multiplicative ℤ)) := by
  show Multiplicative.toAdd (CoprodI.lift abFactor (CoprodI.of y)) = _
  rw [CoprodI.lift_of]
  show Multiplicative.toAdd (parHom (y : Multiplicative ℤ)) = _
  rw [parHom_apply, toAdd_ofAdd]
  rfl

/-! ## 3.  The norm on `ℤ × ℤ` -/

/-- The norm: the source coordinate costs one letter however large it is --
that is the peripheral clause -- and the partner coordinate costs its absolute
value. -/
def abNorm (p : ℤ × ℤ) : ℕ := (if p.1 = 0 then 0 else 1) + p.2.natAbs

@[simp] theorem abNorm_zero : abNorm 0 = 0 := by simp [abNorm]

theorem abNorm_add_le (p q : ℤ × ℤ) : abNorm (p + q) ≤ abNorm p + abNorm q := by
  simp only [abNorm, Prod.fst_add, Prod.snd_add]
  split_ifs <;> omega

@[simp] theorem abNorm_neg (p : ℤ × ℤ) : abNorm (-p) = abNorm p := by
  simp only [abNorm, Prod.fst_neg, Prod.snd_neg, Int.natAbs_neg, neg_eq_zero]

theorem abNorm_le_one_of_snd_eq_zero {p : ℤ × ℤ} (h : p.2 = 0) : abNorm p ≤ 1 := by
  have h2 : p.2.natAbs = 0 := by omega
  simp only [abNorm, h2]
  split_ifs <;> omega

/-! ## 4.  The indicator, as the word norm of the full alphabet -/

theorem isSymmetricGeneratingSet_univ :
    WordMetric.IsSymmetricGeneratingSet (Set.univ : Set (CoprodI Fam)) :=
  ⟨fun _ _ => Set.mem_univ _, Subgroup.closure_univ⟩

/-- **The indicator length**: the word norm of the alphabet consisting of every
element of the group.  It is `0` at the identity and `1` elsewhere, and it comes
with the four length laws already proved. -/
noncomputable def indLen : RelativeLength Fam :=
  ofSymmetricGeneratingSet isSymmetricGeneratingSet_univ (fun _ => Set.mem_univ _)

theorem indLen_le_one (g : CoprodI Fam) : indLen.len g ≤ 1 :=
  WordMetric.wordNorm_le_one_of_mem (Set.mem_univ g)

/-! ## 5.  The length function -/

/-- **The collapsing relative length.**  The indicator supplies "only the
identity is empty"; the abelianisation supplies everything else.  Both factors
are measured exactly -- a partner element `t^k` has length `|k|` -- and the
whole commutator subgroup of the free product has length one. -/
noncomputable def rawLen (g : CoprodI Fam) : ℕ :=
  max (indLen.len g) (abNorm (ab g))

theorem rawLen_def (g : CoprodI Fam) :
    rawLen g = max (indLen.len g) (abNorm (ab g)) := rfl

noncomputable def L : RelativeLength Fam where
  len := rawLen
  len_one := by
    simp only [rawLen_def]
    rw [indLen.len_one, ab_one, abNorm_zero, max_self]
  eq_one_of_len_eq_zero := by
    intro g h
    simp only [rawLen_def] at h
    refine indLen.eq_one_of_len_eq_zero g (Nat.le_zero.mp ?_)
    rw [← h]
    exact le_max_left _ _
  len_mul_le := by
    intro g h
    simp only [rawLen_def]
    refine max_le ?_ ?_
    · exact le_trans (indLen.len_mul_le g h)
        (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
    · rw [ab_mul]
      exact le_trans (abNorm_add_le _ _)
        (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))
  len_inv := by
    intro g
    simp only [rawLen_def]
    rw [indLen.len_inv, ab_inv, abNorm_neg]
  len_source_le_one := by
    intro x
    simp only [rawLen_def]
    refine max_le (indLen_le_one _) ?_
    rw [ab_of_source]
    exact abNorm_le_one_of_snd_eq_zero rfl

theorem L_len (g : CoprodI Fam) :
    L.len g = max (indLen.len g) (abNorm (ab g)) := rfl

theorem abNorm_le_L_len (g : CoprodI Fam) : abNorm (ab g) ≤ L.len g := by
  rw [L_len]
  exact le_max_right _ _

theorem one_le_L_len {g : CoprodI Fam} (hg : g ≠ 1) : 1 ≤ L.len g := by
  rw [L_len]
  exact le_trans (indLen.one_le_len hg) (le_max_left _ _)

/-- **The letters are exactly the elements with short abelianisation.**  One
direction; the alphabet of `L` is therefore not `X ∪ U` for any finite `X`. -/
theorem L_len_le_one_of_abNorm {g : CoprodI Fam} (h : abNorm (ab g) ≤ 1) :
    L.len g ≤ 1 := by
  rw [L_len]
  exact max_le (indLen_le_one g) h

theorem abNorm_le_one_of_L_len {g : CoprodI Fam} (h : L.len g ≤ 1) :
    abNorm (ab g) ≤ 1 :=
  le_trans (abNorm_le_L_len g) h

/-! ## 6.  The two generators -/

/-- The inclusion of the partner factor, as a homomorphism.  The two inclusions
are named because `CoprodI.of (Multiplicative.ofAdd n : Fam true)` does not
elaborate: `Fam true` reduces to a `match` on `Bool`, and the index of
`CoprodI.of` cannot be recovered from it.  Applying a hom whose domain is
already `Fam true` fixes the index, which is
`GGT/RelHypOsinTheorem24Refuted.lean`'s own device. -/
def emT : Fam true →* CoprodI Fam := CoprodI.of

/-- The inclusion of the source factor. -/
def emF : Fam false →* CoprodI Fam := CoprodI.of

/-- The partner's generator. -/
def tLet : CoprodI Fam := emT (Multiplicative.ofAdd (1 : ℤ))

/-- The source's generator. -/
def sLet : CoprodI Fam := emF (Multiplicative.ofAdd (1 : ℤ))

theorem ab_emT (y : Fam true) :
    ab (emT y) = (0, Multiplicative.toAdd (y : Multiplicative ℤ)) :=
  ab_of_partner y

theorem ab_emF (x : Fam false) :
    ab (emF x) = (Multiplicative.toAdd (x : Multiplicative ℤ), 0) :=
  ab_of_source x

@[simp] theorem ab_tLet : ab tLet = (0, 1) := by
  have h := ab_emT (Multiplicative.ofAdd (1 : ℤ))
  rw [toAdd_ofAdd] at h
  exact h

@[simp] theorem ab_sLet : ab sLet = (1, 0) := by
  have h := ab_emF (Multiplicative.ofAdd (1 : ℤ))
  rw [toAdd_ofAdd] at h
  exact h

theorem ab_mul_inv (g e : CoprodI Fam) : ab (g * e⁻¹) = ab g - ab e := by
  rw [ab_mul, ab_inv, sub_eq_add_neg]

theorem ab_snd_mul_tLet_inv (g : CoprodI Fam) :
    (ab (g * tLet⁻¹)).2 = (ab g).2 - 1 := by
  simp only [ab_mul_inv, ab_tLet, Prod.snd_sub]

theorem ab_snd_mul_tLet (g : CoprodI Fam) :
    (ab (g * (tLet⁻¹)⁻¹)).2 = (ab g).2 + 1 := by
  simp only [inv_inv, ab_mul, ab_tLet, Prod.snd_add]

theorem ab_tLet_pow (m : ℕ) : ab (tLet ^ m) = (0, (m : ℤ)) := by
  induction m with
  | zero => simp [Prod.mk_zero_zero]
  | succ k ih =>
      rw [pow_succ, ab_mul, ih, ab_tLet, Prod.mk_add_mk]
      have hc : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [hc, zero_add]

theorem L_len_tLet_le_one : L.len tLet ≤ 1 :=
  L_len_le_one_of_abNorm (by rw [ab_tLet]; simp [abNorm])

theorem L_len_tLet_inv_le_one : L.len tLet⁻¹ ≤ 1 :=
  L_len_le_one_of_abNorm (by rw [ab_inv, abNorm_neg, ab_tLet]; simp [abNorm])

/-- **A power of the partner's generator is measured exactly.**  This is what
`GGT/RelHypOsinTheorem24Refuted.lean`'s witness failed: there `t^42` was a
letter of the alphabet, here it has length `42`. -/
theorem L_len_tLet_pow (m : ℕ) (hm : 1 ≤ m) : L.len (tLet ^ m) = m := by
  have hab : abNorm (ab (tLet ^ m)) = m := by
    rw [ab_tLet_pow]
    simp [abNorm]
  have h1 : indLen.len (tLet ^ m) ≤ 1 := indLen_le_one _
  rw [L_len, hab]
  omega

/-! ## 7.  Geodesic spellings

`HasGeodesicSpellings L` is a hypothesis of every generation of the weighted
leaf, so the witness has to meet it.  It does: peel the partner coordinate one
letter at a time, and absorb the remainder -- which the abelianisation cannot
see, and which is therefore a single letter -- into the head. -/

/-- **Peeling the partner coordinate.**  Every element is a letter `c` whose
abelianisation is `((ab g).1, 0)` followed by exactly `|(ab g).2|` partner
letters. -/
theorem spell_aux : ∀ (k : ℕ) (g : CoprodI Fam), (ab g).2.natAbs = k →
    ∃ c : CoprodI Fam, ∃ l : List (CoprodI Fam),
      (∀ a ∈ l, L.len a ≤ 1) ∧ ab c = ((ab g).1, 0) ∧ c * l.prod = g ∧
        l.length = k := by
  intro k
  induction k with
  | zero =>
      intro g hg
      have h2 : (ab g).2 = 0 := Int.natAbs_eq_zero.mp hg
      exact ⟨g, [], by simp, by simp [Prod.ext_iff, h2], by simp, rfl⟩
  | succ k ih =>
      intro g hg
      have hstep : ∀ e : CoprodI Fam, L.len e ≤ 1 → (ab e).1 = 0 →
          (ab (g * e⁻¹)).2.natAbs = k →
          ∃ c : CoprodI Fam, ∃ l : List (CoprodI Fam),
            (∀ a ∈ l, L.len a ≤ 1) ∧ ab c = ((ab g).1, 0) ∧ c * l.prod = g ∧
              l.length = k + 1 := by
        intro e hlet habe hk
        obtain ⟨c, l, hl, hc, hprod, hlen⟩ := ih (g * e⁻¹) hk
        refine ⟨c, l ++ [e], ?_, ?_, ?_, ?_⟩
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hl a ha
          · rw [List.mem_singleton.mp ha]
            exact hlet
        · rw [hc, ab_mul_inv]
          simp [habe]
        · rw [List.prod_append, List.prod_singleton, ← mul_assoc, hprod]
          simp
        · rw [List.length_append, List.length_singleton, hlen]
      have hb : (ab g).2 ≠ 0 := by omega
      rcases lt_or_gt_of_ne hb with hlt | hgt
      · have h := ab_snd_mul_tLet g
        exact hstep tLet⁻¹ L_len_tLet_inv_le_one (by simp) (by omega)
      · have h := ab_snd_mul_tLet_inv g
        exact hstep tLet L_len_tLet_le_one (by simp) (by omega)

/-- **`L` has geodesic spellings.**  The bound `m.length ≤ L.len g` is enough:
`RelativeLength.len_prod_le` supplies the reverse inequality for any spelling by
letters. -/
theorem hasGeodesicSpellings_L : HasGeodesicSpellings L := by
  intro g
  suffices h : ∃ m : List (CoprodI Fam), (∀ a ∈ m, L.len a ≤ 1) ∧ m.prod = g ∧
      m.length ≤ L.len g by
    obtain ⟨m, hm, hmp, hmlen⟩ := h
    refine ⟨m, hm, hmp, le_antisymm hmlen ?_⟩
    have h2 := L.len_prod_le hm
    rw [hmp] at h2
    exact h2
  obtain ⟨c, l, hl, hc, hprod, hlen⟩ := spell_aux (ab g).2.natAbs g rfl
  have hclet : L.len c ≤ 1 :=
    L_len_le_one_of_abNorm (by rw [hc]; exact abNorm_le_one_of_snd_eq_zero rfl)
  have hle := abNorm_le_L_len g
  by_cases ha : (ab g).1 = 0
  · have hc0 : ab c = 0 := by simp [hc, ha]
    have habg : abNorm (ab g) = (ab g).2.natAbs := by simp [abNorm, ha]
    rcases eq_or_ne c 1 with rfl | hcne
    · refine ⟨l, hl, by simpa using hprod, ?_⟩
      rw [hlen]
      omega
    · rcases l with _ | ⟨e, l'⟩
      · refine ⟨[c], ?_, by simpa using hprod, ?_⟩
        · intro a ha'
          rw [List.mem_singleton.mp ha']
          exact hclet
        · rw [List.length_singleton]
          exact one_le_L_len (by rw [← hprod]; simpa using hcne)
      · refine ⟨(c * e) :: l', ?_, ?_, ?_⟩
        · intro a ha'
          rcases List.mem_cons.mp ha' with rfl | ha'
          · refine L_len_le_one_of_abNorm ?_
            rw [ab_mul, hc0, zero_add]
            exact abNorm_le_one_of_L_len (hl e (by simp))
          · exact hl a (by simp [ha'])
        · rw [List.prod_cons, mul_assoc, ← List.prod_cons, hprod]
        · rw [List.length_cons]
          rw [List.length_cons] at hlen
          omega
  · refine ⟨c :: l, ?_, ?_, ?_⟩
    · intro a ha'
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hclet
      · exact hl a ha'
    · rw [List.prod_cons, hprod]
    · have h1 : abNorm (ab g) = 1 + (ab g).2.natAbs := by simp [abNorm, ha]
      rw [List.length_cons, hlen]
      omega

end Osin24Collapse

end RelHyp
end GGT
end GroupApproximation
