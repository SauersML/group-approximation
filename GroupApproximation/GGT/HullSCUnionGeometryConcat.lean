import GroupApproximation.GGT.HullSCUnionGeometryAcylindrical
import GroupApproximation.Algebra.CoprodIWordInverse

/-!
# The branch lemma in concatenation form

`GGT/HullSCUnionGeometryNormalForm.lean` proves that nothing cancels between two
words that begin in different factors, but records only the *length*:
`|p⁻¹m| = |p| + |m|`.  The induction that proves it in fact builds the reduced
word of `p⁻¹m`, and every statement about the *shape* of a conjugate --- which
syllables of `t` survive in `t⁻¹ k t`, which vertex of the Bass-Serre tree an
element fixes, what a pointwise segment stabiliser is --- needs that word, not
its length.

`toList_equiv_inv_mul_of_fstIdx_ne` records it:

    (p⁻¹m)‾ = invList p‾ ++ m‾

and `toList_equiv_mul_of_seam` is the same read at the back of the left factor,

    (u·y)‾ = u‾ ++ y‾   when the last syllable of `u` and the first of `y`
                          lie in different factors,

which is the form a crossing estimate consumes.  `invList_invList` --- inversion
of reduced words is an involution --- is what carries one into the other, and it
comes free from `CoprodIWordInverse.equiv_inv` rather than from a list
computation.

`exists_split_toList` is `exists_split` with the word-length clause dropped, so
that none of this mentions an alphabet: these are statements about normal forms
alone.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.FreeProductCyclic

section Concat

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-! ## 1.  Splitting the leading syllable, without an alphabet -/

/-- **The normal form of `g`, split at its leading syllable**, recorded as a
`cons` of lists rather than as a sum of word lengths.  This is `exists_split`
with the alphabet removed. -/
theorem exists_split_toList {g : CoprodI G} {i : ι} {u : G i}
    (h : lead g = some ⟨i, u⟩) :
    ∃ g' : CoprodI G, g = CoprodI.of u * g' ∧ u ≠ 1 ∧
      Word.fstIdx (Word.equiv g') ≠ some i ∧
      (Word.equiv g).toList = ⟨i, u⟩ :: (Word.equiv g').toList := by
  unfold lead at h
  obtain ⟨l, hl⟩ : ∃ l, (Word.equiv g).toList = ⟨i, u⟩ :: l :=
    exists_cons_of_head?_eq h
  have hu : u ≠ 1 := (Word.equiv g).ne_one ⟨i, u⟩ (by rw [hl]; simp)
  have hg' : (Word.equiv (CoprodI.of u⁻¹ * g)).toList = l := by
    rw [equiv_of_mul, toList_of_smul u⁻¹ hl, if_pos (inv_mul_cancel u)]
  have hgeq : (CoprodI.of u : CoprodI G) * (CoprodI.of u⁻¹ * g) = g := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have htail : (Word.equivPair i (Word.equiv g)).tail.toList = l :=
    (equivPair_head_of_cons hl).2
  have hword : Word.equiv (CoprodI.of u⁻¹ * g)
      = (Word.equivPair i (Word.equiv g)).tail := Word.ext (by rw [hg', htail])
  have hidx : Word.fstIdx (Word.equiv (CoprodI.of u⁻¹ * g)) ≠ some i := by
    rw [hword]
    exact (Word.equivPair i (Word.equiv g)).fstIdx_ne
  exact ⟨CoprodI.of u⁻¹ * g, hgeq.symm, hu, hidx, by rw [hl, hg']⟩

/-! ## 2.  The concatenation form of the branch lemma -/

/-- **The reduced word of `p⁻¹m` is the concatenation**, when the two words begin
in different factors.  The induction is the one of
`wordNorm_inv_mul_of_fstIdx_ne`, carrying the word rather than its length: the
leading syllable `⟨i,u⟩` of `p` moves to the *end* of `invList p‾`, which is
exactly where `toList_equiv_of_mul` puts `⟨i,u⁻¹⟩` when it is multiplied into
`m`. -/
theorem toList_equiv_inv_mul :
    ∀ (n : ℕ) (p m : CoprodI G), (Word.equiv p).toList.length ≤ n →
      Word.fstIdx (Word.equiv p) ≠ Word.fstIdx (Word.equiv m) →
        (Word.equiv (p⁻¹ * m)).toList
          = CoprodIWordInverse.invList (Word.equiv p).toList
            ++ (Word.equiv m).toList := by
  intro n
  induction n with
  | zero =>
      intro p m hlen _
      have hp : p = 1 := by
        refine sylLength_eq_zero_iff.mp ?_
        have h0 : (Word.equiv p).toList.length = 0 := Nat.le_zero.mp hlen
        simpa [sylLength] using h0
      subst hp
      rw [inv_one, one_mul, equiv_one]
      simp [Word.empty]
  | succ n ih =>
      intro p m hlen hne
      rcases hl : lead p with _ | ⟨i, u⟩
      · have hp : p = 1 := lead_eq_none_iff.mp hl
        subst hp
        rw [inv_one, one_mul, equiv_one]
        simp [Word.empty]
      · obtain ⟨p', hpeq, hu, hp'idx, hp'list⟩ := exists_split_toList hl
        have hfstp : Word.fstIdx (Word.equiv p) = some i := fstIdx_of_lead_some hl
        have hm : Word.fstIdx (Word.equiv m) ≠ some i := by
          intro hcon
          exact hne (by rw [hfstp, hcon])
        have huinv : (u⁻¹ : G i) ≠ 1 := inv_ne_one.mpr hu
        have hm'list : (Word.equiv (CoprodI.of u⁻¹ * m)).toList
            = ⟨i, u⁻¹⟩ :: (Word.equiv m).toList := toList_equiv_of_mul huinv hm
        have hm'fst : Word.fstIdx (Word.equiv (CoprodI.of u⁻¹ * m)) = some i :=
          fstIdx_of_mul huinv hm
        have hlen' : (Word.equiv p').toList.length ≤ n := by
          rw [hp'list] at hlen
          simp only [List.length_cons] at hlen
          omega
        have hstep := ih p' (CoprodI.of u⁻¹ * m) hlen'
          (by rw [hm'fst]; exact hp'idx)
        have hinv : (CoprodI.of u : CoprodI G)⁻¹ = CoprodI.of u⁻¹ :=
          (map_inv (CoprodI.of : G i →* CoprodI G) u).symm
        have hprod : p'⁻¹ * (CoprodI.of u⁻¹ * m) = p⁻¹ * m := by
          have hpi : (p : CoprodI G)⁻¹ = p'⁻¹ * CoprodI.of u⁻¹ := by
            rw [hpeq, mul_inv_rev, hinv]
          rw [hpi, mul_assoc]
        rw [← hprod, hstep, hm'list, hp'list, CoprodIWordInverse.invList_cons]
        simp

/-- **The concatenation form of `wordNorm_branch`.** -/
theorem toList_equiv_inv_mul_of_fstIdx_ne {p m : CoprodI G}
    (h : Word.fstIdx (Word.equiv p) ≠ Word.fstIdx (Word.equiv m)) :
    (Word.equiv (p⁻¹ * m)).toList
      = CoprodIWordInverse.invList (Word.equiv p).toList
        ++ (Word.equiv m).toList :=
  toList_equiv_inv_mul (Word.equiv p).toList.length p m le_rfl h

/-! ## 3.  Inversion of reduced words is an involution -/

/-- **`invList` is an involution on reduced words.**  Not a list computation:
`CoprodIWordInverse.equiv_inv` identifies `invWord` with the normal form of the
inverse, and `inv_inv` does the rest. -/
theorem invList_invList (w : Word G) :
    CoprodIWordInverse.invList (CoprodIWordInverse.invList w.toList) = w.toList := by
  have h3 : Word.equiv (w.prod)⁻¹ = CoprodIWordInverse.invWord (Word.equiv w.prod) :=
    CoprodIWordInverse.equiv_inv _
  rw [equiv_prod] at h3
  have h2 : Word.equiv ((w.prod)⁻¹)⁻¹
      = CoprodIWordInverse.invWord (Word.equiv (w.prod)⁻¹) :=
    CoprodIWordInverse.equiv_inv _
  rw [h3] at h2
  have h1 : Word.equiv ((w.prod)⁻¹)⁻¹ = w := by
    rw [inv_inv]
    exact equiv_prod w
  rw [h1] at h2
  exact congrArg Word.toList h2.symm

/-- **The concatenation form at the back seam.**  If the last syllable of `u`
and the first syllable of `y` lie in different factors, the reduced word of
`u * y` is the concatenation of the two reduced words.  This is the shape a
crossing estimate for `t⁻¹ k t` consumes. -/
theorem toList_equiv_mul_of_seam {u y : CoprodI G}
    (h : Word.fstIdx (Word.equiv u⁻¹) ≠ Word.fstIdx (Word.equiv y)) :
    (Word.equiv (u * y)).toList
      = (Word.equiv u).toList ++ (Word.equiv y).toList := by
  have hb := toList_equiv_inv_mul_of_fstIdx_ne h
  rw [inv_inv, CoprodIWordInverse.equiv_inv, CoprodIWordInverse.invWord_toList,
    invList_invList] at hb
  exact hb

end Concat

end HullSCUnionGeometry
end GroupApproximation
