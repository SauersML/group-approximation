import GroupApproximation.Algebra.CoprodICyclicReduction
import Mathlib.GroupTheory.PushoutI
import Mathlib.Tactic.Group

/-!
# Torsion in an amalgamated free product

**Torsion in an amalgamated free product of groups is conjugate into a factor**
(`exists_conj_into_factor`), and therefore an amalgamated free product of
torsion-free groups is torsion-free (`isPowerTorsionFree_pushoutI`).

This is the amalgam analogue of `Algebra.CoprodICyclicReduction`, and it is
proved by the same three moves over Mathlib's `Monoid.PushoutI.NormalWord`:

* a *nonempty* word none of whose letters lie in the base is not in the base ---
  Mathlib's `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`, the Britton
  analogue.  Every normal word is of that kind, because a transversal meets the
  base only in `1` (`reduced_toWord`);
* a *cyclically* reduced such word --- nonempty, first and last letters in
  different factors --- has all its powers again of that kind, so all its powers
  are nontrivial (`pow_ne_one_of_cyclicallyReduced`);
* *cyclic reduction*: conjugating by the first letter strictly shortens a word
  whose two ends lie in the same factor.

The amalgam differs from the free product in that a normal word carries a base
element in front of the letters, so the length that runs the induction is the
number of non-base syllables (`len`) and the induction has to absorb the base
element into the first letter before conjugating.  The bookkeeping for that ---
that multiplying by a letter changes the syllable count by at most one
(`length_summand_smul_le`), and that no representation of an element as a word
is shorter than its normal word (`len_ofCoprodI_le`) --- is what
`Algebra.CoprodIWordLength` did for the free product; the last step of the
shortening move is read off the free product itself, through
`Algebra.CoprodIWordInverse`.

The consequence needed downstream is the torsion clause of the *image* half of
Higman's Lemma 3.3: `Higman.BenignWitness.mapEmb` builds its witness as an
amalgam, and this is exactly what makes that witness torsion-free.
-/

namespace GroupApproximation
namespace PushoutITorsionFree

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-! ## 1.  Normal words avoid the base -/

/-- **A nonidentity element of the transversal is not in the base.**  The
transversal contains `1`, and it meets each coset of the base once, so the only
element of it inside the base is `1`. -/
theorem notMem_range_of_mem_set {d : NormalWord.Transversal φ} {i : ι} {g : G i}
    (hset : g ∈ d.set i) (hg : g ≠ 1) : g ∉ (φ i).range := by
  intro hmem
  have h1 : (((d.compl i).equiv g).2 : G i) = 1 :=
    ((d.compl i).coe_equiv_snd_eq_one_iff_mem (d.one_mem i)).2 hmem
  have h2 : (((d.compl i).equiv g).2 : G i) = g :=
    ((d.compl i).equiv_snd_eq_self_iff_mem (one_mem _)).2 hset
  exact hg (h2.symm.trans h1)

/-- **Every letter of a normal word avoids the base.** -/
theorem reduced_toWord {d : NormalWord.Transversal φ} (w : NormalWord d) :
    Reduced φ w.toWord := by
  rintro ⟨i, g⟩ hg
  exact notMem_range_of_mem_set (w.normalized i g hg) (w.toWord.ne_one _ hg)

/-- The product of a normal word, spelled out. -/
theorem normalWord_prod {d : NormalWord.Transversal φ} (w : NormalWord d) :
    w.prod = base φ w.head * ofCoprodI w.toWord.prod := rfl

/-! ## 2.  A nonempty word avoiding the base is nontrivial -/

/-- **A nonempty word none of whose letters lies in the base has nontrivial
image in the amalgam.**  If the image were trivial it would lie in the base, and
Mathlib's normal form theorem says only the empty word does. -/
theorem ofCoprodI_prod_ne_one (hφ : ∀ i, Function.Injective (φ i))
    {w : CoprodI.Word G} (hw : Reduced φ w) (hne : w.toList ≠ []) :
    (ofCoprodI w.prod : PushoutI φ) ≠ 1 := by
  intro hcon
  apply hne
  have hmem : (ofCoprodI w.prod : PushoutI φ) ∈ (base φ).range := by
    rw [hcon]
    exact one_mem _
  rw [hw.eq_empty_of_mem_range hφ hmem]
  rfl

/-! ## 3.  Powers of a cyclically reduced word

Mirrors `Algebra.CoprodITorsionFree.neWordPow`; repeated here so that the
statements below carry no decidability instances. -/

/-- The `(n+1)`-st power of a cyclically reduced word, as a nonempty word. -/
def nePow {i j : ι} (hij : j ≠ i) (v : CoprodI.NeWord G i j) : ℕ → CoprodI.NeWord G i j
  | 0 => v
  | n + 1 => (nePow hij v n).append hij v

theorem prod_nePow {i j : ι} (hij : j ≠ i) (v : CoprodI.NeWord G i j) (n : ℕ) :
    (nePow hij v n).prod = v.prod ^ (n + 1) := by
  induction n with
  | zero => simp [nePow]
  | succ n ih =>
      show (CoprodI.NeWord.append (nePow hij v n) hij v).prod = _
      rw [CoprodI.NeWord.append_prod, ih, ← pow_succ]

theorem reduced_nePow {i j : ι} (hij : j ≠ i) (v : CoprodI.NeWord G i j)
    (hv : Reduced φ v.toWord) (n : ℕ) : Reduced φ (nePow hij v n).toWord := by
  induction n with
  | zero => exact hv
  | succ n ih =>
      intro l hl
      have hmem : l ∈ (nePow hij v n).toList ++ v.toList := hl
      rcases List.mem_append.1 hmem with h | h
      · exact ih l h
      · exact hv l h

/-- **A cyclically reduced word avoiding the base has infinite order in the
amalgam.**  Its powers are again cyclically reduced words avoiding the base, and
those are nontrivial. -/
theorem pow_ne_one_of_cyclicallyReduced (hφ : ∀ i, Function.Injective (φ i))
    {i j : ι} (hij : j ≠ i) (v : CoprodI.NeWord G i j) (hv : Reduced φ v.toWord)
    (n : ℕ) : (ofCoprodI v.prod : PushoutI φ) ^ (n + 1) ≠ 1 := by
  have hkey : (ofCoprodI ((nePow hij v n).prod) : PushoutI φ) ≠ 1 :=
    ofCoprodI_prod_ne_one hφ (reduced_nePow hij v hv n)
      (CoprodI.NeWord.toList_ne_nil (nePow hij v n))
  rw [prod_nePow, map_pow] at hkey
  exact hkey

/-- Appending a letter outside the base to a word avoiding the base again
avoids the base. -/
theorem reduced_append_singleton {a b i : ι} (v : CoprodI.NeWord G a b) (hb : b ≠ i)
    {m : G i} (hm1 : m ≠ 1) (hv : Reduced φ v.toWord) (hm : m ∉ (φ i).range) :
    Reduced φ (v.append hb (CoprodI.NeWord.singleton m hm1)).toWord := by
  intro l hl
  have hmem : l ∈ v.toList ++ [(⟨i, m⟩ : Σ i, G i)] := hl
  rcases List.mem_append.1 hmem with h | h
  · exact hv l h
  · rw [List.mem_singleton] at h
    subst h
    exact hm

/-! ## 4.  Splitting off the first letter of a word -/

theorem exists_cons : ∀ w : CoprodI.Word G, w.toList ≠ [] →
    ∃ (i : ι) (g : G i) (w' : CoprodI.Word G) (h1 : w'.fstIdx ≠ some i) (h2 : g ≠ 1),
      w = CoprodI.Word.cons g w' h1 h2 := by
  intro w
  induction w using CoprodI.Word.consRecOn with
  | empty => intro hw; exact absurd rfl hw
  | cons i g w' h1 h2 _ => intro _; exact ⟨i, g, w', h1, h2, rfl⟩

/-! ## 5.  The syllable length of an element of the amalgam -/

section Length

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

theorem equiv_prod (w : CoprodI.Word G) :
    CoprodI.Word.equiv (CoprodI.Word.prod w) = w :=
  CoprodI.Word.equiv.apply_symm_apply w

/-- **Multiplying on the right by a letter of the summand the word already ends
in does not increase its length.**  Read off the inverse word, where it is the
statement of `Algebra.CoprodIWordLength` about the first letter. -/
theorem length_equiv_mul_of_le (z : CoprodI G) {i : ι} (m : G i)
    (hlast : (CoprodI.Word.equiv z).toList.getLast?.map Sigma.fst = some i) :
    (CoprodI.Word.equiv (z * CoprodI.of m)).toList.length
      ≤ (CoprodI.Word.equiv z).toList.length := by
  have hinv : CoprodI.Word.fstIdx (CoprodI.Word.equiv z⁻¹) = some i := by
    rw [CoprodIWordInverse.fstIdx_inv]
    exact hlast
  have hz : (CoprodI.Word.equiv ((z * CoprodI.of m)⁻¹)).toList.length
      ≤ (CoprodI.Word.equiv z⁻¹).toList.length := by
    have hrw : (z * CoprodI.of m)⁻¹ = CoprodI.of m⁻¹ * z⁻¹ := by
      rw [mul_inv_rev, ← map_inv]
    rw [hrw, CoprodICyclicReduction.equiv_of_mul]
    exact CoprodIWordLength.length_smul_le_of_fstIdx _ _ hinv
  calc (CoprodI.Word.equiv (z * CoprodI.of m)).toList.length
      = (CoprodI.Word.equiv ((z * CoprodI.of m)⁻¹)).toList.length :=
        (CoprodIWordInverse.length_equiv_inv _).symm
    _ ≤ (CoprodI.Word.equiv z⁻¹).toList.length := hz
    _ = (CoprodI.Word.equiv z).toList.length := CoprodIWordInverse.length_equiv_inv z

/-- The number of non-base syllables of an element of the amalgam. -/
noncomputable def len (d : NormalWord.Transversal φ) (x : PushoutI φ) : ℕ :=
  (NormalWord.equiv x : NormalWord d).toList.length

theorem len_one (d : NormalWord.Transversal φ) : len d (1 : PushoutI φ) = 0 := by
  have h : (NormalWord.equiv (1 : PushoutI φ) : NormalWord d)
      = (NormalWord.empty : NormalWord d) := by
    show (1 : PushoutI φ) • (NormalWord.empty : NormalWord d)
        = (NormalWord.empty : NormalWord d)
    exact one_smul _ _
  rw [len, h]
  rfl

/-- The tail of the amalgam's pair decomposition is the tail of the free
product's. -/
theorem equivPair_tail_eq {d : NormalWord.Transversal φ} (i : ι) (w : NormalWord d) :
    (NormalWord.equivPair i w).tail = (CoprodI.Word.equivPair i w.toWord).tail := by
  show (CoprodI.Word.equivPair i (CoprodI.of (φ i w.head) • w.toWord)).tail = _
  rw [CoprodI.Word.equivPair_smul_same]

/-- Prepending a head to a pair adds at most one syllable. -/
theorem length_equivPair_symm_le {d : NormalWord.Transversal φ} (i : ι)
    (p : NormalWord.Pair d i) :
    ((NormalWord.equivPair i).symm p : NormalWord d).toList.length
      ≤ p.tail.toList.length + 1 :=
  CoprodIWordLength.length_rcons_le
    ({ p.toPair with head := (((d.compl i).equiv p.head).2 : G i) } :
      CoprodI.Word.Pair G i)

/-- **Multiplying by a letter changes the syllable count by at most one.** -/
theorem length_summand_smul_le {d : NormalWord.Transversal φ} {i : ι} (g : G i)
    (w : NormalWord d) :
    (g • w).toList.length ≤ w.toList.length + 1 := by
  rw [NormalWord.summand_smul_def']
  refine le_trans (length_equivPair_symm_le i _) ?_
  have h : ({ NormalWord.equivPair i w with
        head := g * (NormalWord.equivPair i w).head } : NormalWord.Pair d i).tail
      = (CoprodI.Word.equivPair i w.toWord).tail := equivPair_tail_eq i w
  rw [h]
  exact Nat.succ_le_succ (CoprodIWordLength.length_equivPair_tail_le i w.toWord)

theorem len_of_mul_le (d : NormalWord.Transversal φ) (i : ι) (g : G i)
    (x : PushoutI φ) : len d (of (φ := φ) i g * x) ≤ len d x + 1 := by
  have h : (NormalWord.equiv (of (φ := φ) i g * x) : NormalWord d)
      = g • (NormalWord.equiv x : NormalWord d) := by
    show (of (φ := φ) i g * x) • (NormalWord.empty : NormalWord d)
        = g • ((x : PushoutI φ) • (NormalWord.empty : NormalWord d))
    rw [mul_smul, NormalWord.of_smul_eq_smul]
  rw [len, len, h]
  exact length_summand_smul_le g _

/-- **No word representing an element is shorter than its normal word.** -/
theorem len_ofCoprodI_le (d : NormalWord.Transversal φ) (w : CoprodI.Word G) :
    len d (ofCoprodI w.prod : PushoutI φ) ≤ w.toList.length := by
  induction w using CoprodI.Word.consRecOn with
  | empty =>
      have h : (ofCoprodI (CoprodI.Word.empty : CoprodI.Word G).prod : PushoutI φ) = 1 := by
        rw [CoprodI.Word.prod_empty, map_one]
      rw [h, len_one]
      exact Nat.zero_le _
  | cons i g w h1 h2 ih =>
      have hp : (ofCoprodI (CoprodI.Word.cons g w h1 h2).prod : PushoutI φ)
          = of (φ := φ) i g * ofCoprodI w.prod := by
        rw [CoprodI.Word.prod_cons, map_mul, ofCoprodI_of]
      have hl : (CoprodI.Word.cons g w h1 h2).toList.length = w.toList.length + 1 := by
        simp [CoprodI.Word.cons]
      rw [hp, hl]
      exact le_trans (len_of_mul_le d i g _) (Nat.succ_le_succ ih)

/-- **The normal form, read as a word avoiding the base of the shortest possible
length.** -/
theorem exists_reduced_word (d : NormalWord.Transversal φ) (x : PushoutI φ) :
    ∃ (h : H) (w : CoprodI.Word G), Reduced φ w ∧ w.toList.length = len d x ∧
      x = base φ h * ofCoprodI w.prod := by
  refine ⟨(NormalWord.equiv x : NormalWord d).head,
    (NormalWord.equiv x : NormalWord d).toWord, reduced_toWord _, rfl, ?_⟩
  have h : (NormalWord.equiv (d := d) x).prod = x :=
    NormalWord.equiv.symm_apply_apply x
  exact ((normalWord_prod _).symm.trans h).symm

end Length

/-! ## 6.  Conjugating into a factor -/

theorem pow_conj_eq_one {x c : PushoutI φ} {n : ℕ} (hxn : x ^ n = 1) :
    (c * x * c⁻¹) ^ n = 1 := by
  rw [conj_pow, hxn, mul_one, mul_inv_cancel]

theorem conj_of_mem_base_range {x : PushoutI φ} (i : ι) (hx : x ∈ (base φ).range) :
    ∃ (c : PushoutI φ) (j : ι) (m : G j), c * x * c⁻¹ = of (φ := φ) j m := by
  obtain ⟨h, rfl⟩ := hx
  refine ⟨1, i, φ i h, ?_⟩
  rw [of_apply_eq_base]
  group

theorem conj_transfer {x : PushoutI φ} (c : PushoutI φ)
    (hy : ∃ (g : PushoutI φ) (j : ι) (m : G j),
      g * (c * x * c⁻¹) * g⁻¹ = of (φ := φ) j m) :
    ∃ (g : PushoutI φ) (j : ι) (m : G j), g * x * g⁻¹ = of (φ := φ) j m := by
  obtain ⟨g, j, m, hg⟩ := hy
  refine ⟨g * c, j, m, ?_⟩
  rw [← hg]
  group

section Main

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- **Torsion in an amalgamated free product is conjugate into a factor**, by
induction on the syllable length.

Write `x` as a base element times a word avoiding the base.  If the word is
empty, `x` is in the base.  Otherwise absorb the base element into the first
letter, giving `x = of i m * ofCoprodI w'.prod` with `m` outside the base.  If
`w'` is empty, `x` is already in a factor.  If the last letter of `w'` lies in a
factor other than `i`, then conjugating `x` by `of i m` produces a *cyclically*
reduced word, all of whose powers are nontrivial --- so this cannot happen for
an `x` of finite order.  In the remaining case the conjugate is shorter, and the
induction hypothesis applies to it. -/
theorem exists_conj_into_factor_aux (hφ : ∀ i, Function.Injective (φ i))
    (d : NormalWord.Transversal φ) (p : ℕ) :
    ∀ (k : ℕ) (x : PushoutI φ), len d x ≤ k → x ^ (p + 1) = 1 →
      x ∈ (base φ).range ∨
        ∃ (c : PushoutI φ) (j : ι) (m : G j), c * x * c⁻¹ = of (φ := φ) j m := by
  intro k
  induction k with
  | zero =>
      intro x hx _
      left
      obtain ⟨h, w, _, hlen, hxeq⟩ := exists_reduced_word d x
      have hw : w.toList = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hprod : w.prod = 1 := by simp [CoprodI.Word.prod, hw]
      exact ⟨h, by rw [hxeq, hprod, map_one, mul_one]⟩
  | succ k ih =>
      intro x hx hxn
      obtain ⟨h, w, hred, hlen, hxeq⟩ := exists_reduced_word d x
      by_cases hw : w.toList = []
      · left
        have hprod : w.prod = 1 := by simp [CoprodI.Word.prod, hw]
        exact ⟨h, by rw [hxeq, hprod, map_one, mul_one]⟩
      · obtain ⟨i, g, w', h1, h2, rfl⟩ := exists_cons w hw
        obtain ⟨mm, hmm⟩ : ∃ mm : G i, φ i h * g = mm := ⟨_, rfl⟩
        have hgr : g ∉ (φ i).range := hred ⟨i, g⟩ (by simp [CoprodI.Word.cons])
        have hmr : mm ∉ (φ i).range := by
          rintro ⟨t, ht⟩
          refine hgr ⟨h⁻¹ * t, ?_⟩
          rw [map_mul, map_inv, ht, ← hmm]
          group
        have hm1 : mm ≠ 1 := by
          intro hc
          exact hmr (by rw [hc]; exact one_mem _)
        have hxm : x = of (φ := φ) i mm * ofCoprodI w'.prod := by
          rw [hxeq, CoprodI.Word.prod_cons, map_mul, ofCoprodI_of,
            ← of_apply_eq_base φ i, ← mul_assoc, ← map_mul, hmm]
        have hw'red : Reduced φ w' := fun l hl => hred l (List.mem_cons_of_mem _ hl)
        by_cases hw' : w'.toList = []
        · right
          have hprod : (ofCoprodI w'.prod : PushoutI φ) = 1 := by
            have hz : w'.prod = 1 := by simp [CoprodI.Word.prod, hw']
            rw [hz, map_one]
          refine ⟨1, i, mm, ?_⟩
          rw [hxm, hprod, mul_one]
          group
        · obtain ⟨a, b, v, hv⟩ :=
            CoprodI.NeWord.of_word w' (fun hc => hw' (by rw [hc]; rfl))
          have hvp : v.prod = w'.prod := congrArg CoprodI.Word.prod hv
          have hfst : w'.fstIdx = some a := by
            rw [← hv]
            show (CoprodI.NeWord.toList v).head?.map Sigma.fst = some a
            rw [CoprodI.NeWord.toList_head?]
            rfl
          have hlast : w'.toList.getLast?.map Sigma.fst = some b := by
            rw [← hv]
            show (CoprodI.NeWord.toList v).getLast?.map Sigma.fst = some b
            rw [CoprodI.NeWord.toList_getLast?]
            rfl
          have hai : a ≠ i := by
            intro hc
            exact h1 (by rw [hfst, hc])
          have hvred : Reduced φ v.toWord := by rw [hv]; exact hw'red
          by_cases hbi : b = i
          · -- the two ends share a factor: conjugating shortens
            rw [hbi] at hlast
            have hy : (ofCoprodI (w'.prod * CoprodI.of mm) : PushoutI φ)
                = (of (φ := φ) i mm)⁻¹ * x * ((of (φ := φ) i mm)⁻¹)⁻¹ := by
              rw [map_mul, ofCoprodI_of, hxm]
              group
            have hstep : (CoprodI.Word.equiv (w'.prod * CoprodI.of mm)).toList.length
                ≤ w'.toList.length := by
              have hz := length_equiv_mul_of_le w'.prod mm (by rw [equiv_prod]; exact hlast)
              rwa [equiv_prod] at hz
            have hbound := len_ofCoprodI_le d (CoprodI.Word.equiv (w'.prod * CoprodI.of mm))
            rw [CoprodICyclicReduction.prod_equiv] at hbound
            have hcons : (CoprodI.Word.cons g w' h1 h2).toList.length
                = w'.toList.length + 1 := by simp [CoprodI.Word.cons]
            rw [hcons] at hlen
            have hylen : len d ((of (φ := φ) i mm)⁻¹ * x * ((of (φ := φ) i mm)⁻¹)⁻¹) ≤ k := by
              rw [← hy]
              omega
            have hyn : ((of (φ := φ) i mm)⁻¹ * x * ((of (φ := φ) i mm)⁻¹)⁻¹) ^ (p + 1) = 1 :=
              pow_conj_eq_one hxn
            right
            refine conj_transfer (of (φ := φ) i mm)⁻¹ ?_
            rcases ih _ hylen hyn with hbb | hbb
            · exact conj_of_mem_base_range i hbb
            · exact hbb
          · -- the two ends lie in different factors: infinite order
            exfalso
            have hred' :
                Reduced φ (v.append hbi (CoprodI.NeWord.singleton mm hm1)).toWord :=
              reduced_append_singleton v hbi hm1 hvred hmr
            have hy : (ofCoprodI (v.append hbi (CoprodI.NeWord.singleton mm hm1)).prod :
                  PushoutI φ)
                = (of (φ := φ) i mm)⁻¹ * x * ((of (φ := φ) i mm)⁻¹)⁻¹ := by
              rw [CoprodI.NeWord.append_prod, CoprodI.NeWord.prod_singleton, hvp,
                map_mul, ofCoprodI_of, hxm]
              group
            refine pow_ne_one_of_cyclicallyReduced hφ (Ne.symm hai)
              (v.append hbi (CoprodI.NeWord.singleton mm hm1)) hred' p ?_
            rw [hy]
            exact pow_conj_eq_one hxn

end Main

/-! ## 7.  The theorem -/

/-- **Torsion in an amalgamated free product is conjugate into a factor.**

`x` is either in the amalgamated subgroup or conjugate into one of the two
factors.  No hypothesis on the factors is needed; only that the maps of the
diagram are injective, which is what makes the pushout an amalgam. -/
theorem exists_conj_into_factor (hφ : ∀ i, Function.Injective (φ i))
    {x : PushoutI φ} {n : ℕ} (hn : 0 < n) (hxn : x ^ n = 1) :
    x ∈ (base φ).range ∨
      ∃ (c : PushoutI φ) (j : ι) (m : G j), c * x * c⁻¹ = of (φ := φ) j m := by
  classical
  obtain ⟨d⟩ := NormalWord.transversal_nonempty φ hφ
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact exists_conj_into_factor_aux hφ d p (len d x) x le_rfl hxn

/-- **An amalgamated free product of torsion-free groups is torsion-free.** -/
theorem isPowerTorsionFree_pushoutI (hφ : ∀ i, Function.Injective (φ i))
    (hfac : ∀ i, IsPowerTorsionFree (G i)) (hbase : IsPowerTorsionFree H) :
    IsPowerTorsionFree (PushoutI φ) := by
  intro x n hn hxn
  rcases exists_conj_into_factor hφ hn hxn with ⟨h, rfl⟩ | ⟨c, j, m, hc⟩
  · have hpow : (base φ) (h ^ n) = (base φ) 1 := by
      rw [map_pow, map_one]
      exact hxn
    rw [hbase h n hn (base_injective hφ hpow), map_one]
  · have hpow : (of (φ := φ) j m) ^ n = 1 := by
      rw [← hc]
      exact pow_conj_eq_one hxn
    have hm : m ^ n = 1 := by
      refine of_injective hφ j ?_
      rw [map_pow, map_one]
      exact hpow
    have hone : c * x * c⁻¹ = 1 := by
      rw [hc, hfac j m n hn hm, map_one]
    have hback := congrArg (fun z => c⁻¹ * z * c) hone
    simpa [mul_assoc] using hback

/-- **An amalgamated free product of torsion-free groups is torsion-free**, with
the hypothesis on the amalgamated subgroup dropped: it embeds in a factor. -/
theorem isPowerTorsionFree_pushoutI_of_nonempty [Nonempty ι]
    (hφ : ∀ i, Function.Injective (φ i))
    (hfac : ∀ i, IsPowerTorsionFree (G i)) :
    IsPowerTorsionFree (PushoutI φ) :=
  isPowerTorsionFree_pushoutI hφ hfac
    (IsPowerTorsionFree.comap (hfac (Classical.arbitrary ι)) (φ (Classical.arbitrary ι))
      (hφ (Classical.arbitrary ι)))

end PushoutITorsionFree
end GroupApproximation
