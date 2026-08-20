import GroupApproximation.Algebra.CoprodIWordLength
import GroupApproximation.Algebra.CoprodIWordInverse
import GroupApproximation.Algebra.CoprodITorsionFree

/-!
# Cyclic reduction, and torsion-freeness of a free product

The two preceding files supply what Mathlib's head-oriented normal form lacks:
`Algebra.CoprodIWordInverse` reads the last letter of `x` as the first letter of
`x⁻¹`, and `Algebra.CoprodIWordLength` bounds how the length moves under left
multiplication by a letter.  With both, the classical argument goes through.

**The move.**  If the reduced word of `y` has length at least two and its first
and last letters lie in the *same* summand `M i`, conjugating by the first
letter `m` strictly shortens it: `(of m)⁻¹ * y` drops the first letter, and
multiplying that on the right by `of m` merges into the last letter, which is
also in `M i`.  The right-hand multiplication is read off the inverse, where it
is a left multiplication.

**The consequence.**  Iterating, every element is conjugate either to a single
letter or to a word whose ends lie in different summands --- and the latter has
infinite order by `Algebra.CoprodITorsionFree.prod_pow_ne_one`.  So a free
product of torsion-free groups is torsion-free, which is the Kurosh-type fact
this repository has routed around since `Monsters.ChiodoTorsionFreeAbsorber`
and which `Higman.CountableToFG` needs for its torsion clause.
-/

namespace GroupApproximation
namespace CoprodICyclicReduction

open Monoid Monoid.CoprodI

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Group (M i)]
  [∀ i, DecidableEq (M i)]

/-! ## 1.  Bridging `Word.equiv` -/

theorem prod_equiv (x : CoprodI M) : Word.prod (Word.equiv x) = x :=
  Word.equiv.symm_apply_apply x

theorem equiv_of_mul {i : ι} (m : M i) (x : CoprodI M) :
    Word.equiv (CoprodI.of m * x) = m • Word.equiv x := by
  show (CoprodI.of m * x) • Word.empty = _
  rw [mul_smul, Word.of_smul_eq_smul]
  rfl

theorem equiv_eq_empty_iff (x : CoprodI M) :
    Word.equiv x = Word.empty ↔ x = 1 := by
  constructor
  · intro h
    have h' := congrArg Word.prod h
    rwa [prod_equiv, Word.prod_empty] at h'
  · rintro rfl
    show (1 : CoprodI M) • Word.empty = Word.empty
    exact one_smul _ _

theorem toList_ne_nil_of_ne_one {x : CoprodI M} (hx : x ≠ 1) :
    (Word.equiv x).toList ≠ [] := by
  intro h
  exact hx ((equiv_eq_empty_iff x).1 (Word.ext h))

/-- **A nonempty reduced word is not the identity**, stated for `Word` rather
than `NeWord`.

`FreeProductOrder.neWord_prod_ne_one` says the same for `NeWord`, and that is
the form the alternating-product constructions use; but for *building* a
witness it is easier to exhibit a `Word` --- a list together with `ne_one` and
`chain_ne` --- than to assemble a `NeWord` out of `singleton` and `append`.
This version removes that detour: to show a product in a free product is
nontrivial it is enough to exhibit its reduced word and observe it is
nonempty. -/
theorem prod_ne_one_of_toList_ne_nil {w : Word M} (h : w.toList ≠ []) :
    Word.prod w ≠ 1 := by
  intro hp
  apply h
  have hback : Word.equiv (Word.prod w) = w := Word.equiv.apply_symm_apply w
  rw [hp, (equiv_eq_empty_iff (1 : CoprodI M)).2 rfl] at hback
  rw [← hback]
  rfl

/-! ## 2.  Splitting off the first letter -/

theorem equivPair_tail_toList {i : ι} (w : Word M) (h : Word.fstIdx w = some i) :
    (Word.equivPair i w).tail.toList = w.toList.tail := by
  have hw : Word.rcons (Word.equivPair i w) = w :=
    CoprodIWordLength.rcons_equivPair i w
  by_cases hhead : (Word.equivPair i w).head = 1
  · exfalso
    rw [Word.rcons, dif_pos hhead] at hw
    exact (Word.equivPair i w).fstIdx_ne (by rw [hw]; exact h)
  · conv_rhs => rw [← hw]
    rw [Word.rcons, dif_neg hhead]
    simp [Word.cons]

/-- Multiplying on the left by the inverse of the first letter drops it. -/
theorem equiv_head_inv_mul {i : ι} (x : CoprodI M)
    (h : Word.fstIdx (Word.equiv x) = some i) :
    Word.equiv (CoprodI.of ((Word.equivPair i (Word.equiv x)).head)⁻¹ * x)
      = (Word.equivPair i (Word.equiv x)).tail := by
  rw [equiv_of_mul, Word.smul_def]
  simp [Word.rcons]

/-! ## 3.  The shortening move -/

/-- **Conjugating by the first letter strictly shortens a word whose ends lie
in the same summand.** -/
theorem exists_conj_shorter {i : ι} (y : CoprodI M)
    (hlen : 2 ≤ (Word.equiv y).toList.length)
    (hfst : Word.fstIdx (Word.equiv y) = some i)
    (hlast : ((Word.equiv y).toList.getLast?).map Sigma.fst = some i) :
    ∃ g : CoprodI M,
      (Word.equiv (g * y * g⁻¹)).toList.length < (Word.equiv y).toList.length := by
  set W := Word.equiv y with hW
  set m := (Word.equivPair i W).head with hm
  refine ⟨CoprodI.of m⁻¹, ?_⟩
  set t := CoprodI.of m⁻¹ * y with ht
  have htw : Word.equiv t = (Word.equivPair i W).tail := equiv_head_inv_mul y hfst
  have htlen : (Word.equiv t).toList.length = W.toList.length - 1 := by
    rw [htw]
    have := CoprodIWordLength.length_eq_of_fstIdx i W hfst
    omega
  have htlast : ((Word.equiv t).toList.getLast?).map Sigma.fst = some i := by
    rw [htw, equivPair_tail_toList W hfst]
    rcases hL : W.toList with _ | ⟨a, L'⟩
    · rw [hL] at hlen; simp at hlen
    · rcases hL' : L' with _ | ⟨b, L''⟩
      · rw [hL, hL'] at hlen; simp at hlen
      · rw [hL, hL'] at hlast ⊢
        simpa using hlast
  have hinv : Word.fstIdx (Word.equiv t⁻¹) = some i := by
    rw [CoprodIWordInverse.fstIdx_inv]
    exact htlast
  have hyconj : CoprodI.of m⁻¹ * y * (CoprodI.of m⁻¹)⁻¹ = t * CoprodI.of m := by
    rw [ht]
    simp [mul_assoc]
  have hzinv : (t * CoprodI.of m)⁻¹ = CoprodI.of m⁻¹ * t⁻¹ := by
    simp [mul_inv_rev]
  have hz : (Word.equiv ((t * CoprodI.of m)⁻¹)).toList.length
      ≤ (Word.equiv t⁻¹).toList.length := by
    rw [hzinv, equiv_of_mul]
    exact CoprodIWordLength.length_smul_le_of_fstIdx _ _ hinv
  have hlen2 : (Word.equiv (t * CoprodI.of m)).toList.length
      ≤ W.toList.length - 1 := by
    rw [← CoprodIWordInverse.length_equiv_inv]
    calc (Word.equiv ((t * CoprodI.of m)⁻¹)).toList.length
        ≤ (Word.equiv t⁻¹).toList.length := hz
      _ = (Word.equiv t).toList.length := CoprodIWordInverse.length_equiv_inv t
      _ = W.toList.length - 1 := htlen
  rw [hyconj]
  omega

/-! ## 4.  Torsion-freeness of a free product -/

theorem eq_of_toList_singleton {y : CoprodI M} {a : Σ i, M i}
    (h : (Word.equiv y).toList = [a]) : y = CoprodI.of a.2 := by
  have hp := prod_equiv y
  rw [← hp, Word.prod, h]
  simp

theorem exists_neWord {y : CoprodI M} (hy : y ≠ 1) :
    ∃ (i j : ι) (w : NeWord M i j), w.prod = y ∧
      Word.fstIdx (Word.equiv y) = some i ∧
      ((Word.equiv y).toList.getLast?).map Sigma.fst = some j := by
  obtain ⟨i, j, w, hw⟩ :=
    NeWord.of_word (Word.equiv y) (fun h => hy ((equiv_eq_empty_iff y).1 h))
  refine ⟨i, j, w, ?_, ?_, ?_⟩
  · show Word.prod w.toWord = y
    rw [hw]
    exact prod_equiv y
  · show ((Word.equiv y).toList.head?).map Sigma.fst = some i
    rw [← hw]
    show ((w.toList).head?).map Sigma.fst = some i
    rw [w.toList_head?]
    rfl
  · rw [← hw]
    show ((w.toList).getLast?).map Sigma.fst = some j
    rw [w.toList_getLast?]
    rfl

/-- **A free product of torsion-free groups is torsion-free.** -/
theorem isPowerTorsionFree_coprodI (hfac : ∀ i, IsPowerTorsionFree (M i)) :
    IsPowerTorsionFree (CoprodI M) := by
  intro x n hn hxn
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  suffices H : ∀ (k : ℕ) (y : CoprodI M),
      (Word.equiv y).toList.length ≤ k → y ^ (p + 1) = 1 → y = 1 by
    exact H _ x le_rfl hxn
  intro k
  induction k with
  | zero =>
      intro y hy _
      by_contra hne
      exact toList_ne_nil_of_ne_one hne
        (List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hy))
  | succ k ih =>
      intro y hy hyn
      by_contra hne
      obtain ⟨i, j, w, hwprod, hfst, hlast⟩ := exists_neWord hne
      by_cases hij : j = i
      · subst hij
        by_cases hlen : 2 ≤ (Word.equiv y).toList.length
        · obtain ⟨g, hg⟩ := exists_conj_shorter y hlen hfst hlast
          have hconj : (g * y * g⁻¹) ^ (p + 1) = 1 := by
            rw [conj_pow, hyn, mul_one, mul_inv_cancel]
          have hgy : g * y * g⁻¹ = 1 := ih _ (by omega) hconj
          refine hne ?_
          have := congrArg (fun z ↦ g⁻¹ * z * g) hgy
          simpa [mul_assoc] using this
        · push_neg at hlen
          have hnil := toList_ne_nil_of_ne_one hne
          rcases hL : (Word.equiv y).toList with _ | ⟨a, L⟩
          · exact hnil hL
          · have hLnil : L = [] := by
              rw [hL] at hlen
              simpa using Nat.lt_succ_iff.mp hlen
            have hy_eq : y = CoprodI.of a.2 := by
              refine eq_of_toList_singleton ?_
              rw [hL, hLnil]
            have ha : a.2 ^ (p + 1) = 1 := by
              apply CoprodI.of_injective a.1
              rw [map_pow, map_one, ← hy_eq]
              exact hyn
            have ha1 : a.2 = 1 := hfac a.1 a.2 (p + 1) (Nat.succ_pos p) ha
            exact (Word.equiv y).ne_one a (by rw [hL]; exact List.mem_cons_self ..) ha1
      · exact CoprodITorsionFree.prod_pow_ne_one hij w p (by rw [hwprod]; exact hyn)

end CoprodICyclicReduction
end GroupApproximation
