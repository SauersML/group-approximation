import GroupApproximation.Sofic.GreendlingerNormalForm

/-!
# The one-relator Greendlinger conclusion

`GreendlingerNormalForm` closes the palindromic conjugation normal form: every
conjugate of a cyclically reduced nonempty word is spelled by a *reduced*
palindrome around a rotation of that word.  This file reads off the consequence
that the gate's statement is about.

`GreendlingerConclusion R` asks that every nonempty reduced word in the normal
closure of the relators contain, as a contiguous subword, **more than half** of
some symmetrized relator.  In the one-relator case -- when the word spells a
single conjugate of a symmetrized relator, which is what a minimal expression
with one factor gives -- the conclusion holds in the strongest possible form:
the word contains a *whole* symmetrized relator, not merely more than half of
one.

## Why it is immediate from the normal form

A conjugate of `s` is spelled by a reduced `palindrome c (s.rotate k)`.  Reduced
words spelling the same free-group element are equal, so that palindrome *is*
the given word `w`.  The rotation sits inside it by construction, and
`symmetrization` is closed under rotation, so the rotation is itself a
symmetrized relator.  Taking the subword to be the whole rotation, the required
inequality `t.length < 2 * u.length` reads `|t| < 2|t|`, which is just
nonemptiness.

That last point is where the hypothesis that relators are nonempty is spent, and
it is the only place: `ne_nil_of_mem_symmetrization` carries it to the
symmetrization through `invRev_length`.

Unconditional; nothing here depends on the gate.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-- The symmetrization of a family of nonempty relators consists of nonempty
words. -/
theorem ne_nil_of_mem_symmetrization {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) {w : List (α × Bool)}
    (hw : w ∈ symmetrization R) : w ≠ [] := by
  obtain ⟨r, hr, k, h | h⟩ := hw
  · rw [h]
    exact fun hcon => hRne r hr (List.rotate_eq_nil_iff.mp hcon)
  · rw [h]
    intro hcon
    have h0 : FreeGroup.invRev r = [] := List.rotate_eq_nil_iff.mp hcon
    have hlen : r.length = 0 := by
      rw [← FreeGroup.invRev_length, h0]
      rfl
    exact hRne r hr (List.length_eq_zero_iff.mp hlen)

/-- **The one-relator Greendlinger conclusion.**  A reduced word spelling a
conjugate of a symmetrized relator contains that relator, up to rotation, as a
contiguous subword.

This is stronger than the conclusion the gate asks for: the word contains a
*whole* symmetrized relator, where the gate needs only more than half of one. -/
theorem greendlinger_of_isConj {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {s : List (α × Bool)} (hs : s ∈ symmetrization R)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (hconj : IsConj (FreeGroup.mk s) (FreeGroup.mk w)) :
    ∃ t ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: t ∧ t.length < 2 * u.length := by
  have hscyc : FreeGroup.IsCyclicallyReduced s :=
    symmetrization_isCyclicallyReduced hR hs
  have hsne : s ≠ [] := ne_nil_of_mem_symmetrization hRne hs
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  obtain ⟨L, hL⟩ : ∃ L, FreeGroup.mk L = g := ⟨g.toWord, FreeGroup.mk_toWord⟩
  obtain ⟨c, k, hpred, hpeq⟩ := exists_conjugation_normalForm hscyc hsne L
  -- the conjugate is spelled by a reduced palindrome, so it *is* `w`
  have hmk : FreeGroup.mk w = FreeGroup.mk (palindrome c (s.rotate k)) := by
    rw [← hg, ← hL, hpeq]
  have hwe : w = palindrome c (s.rotate k) := by
    have h1 := FreeGroup.reduce.sound hmk
    rwa [hw.reduce_eq, hpred.reduce_eq] at h1
  refine ⟨s.rotate k, rotate_mem_symmetrization hs k, s.rotate k, ?_,
    List.prefix_refl _, ?_⟩
  · rw [hwe]
    exact ⟨c, FreeGroup.invRev c, rfl⟩
  · have hlen : 0 < (s.rotate k).length := by
      rw [List.length_rotate]
      exact List.length_pos_iff.mpr hsne
    omega

/-- The same, keyed to a relator of the family. -/
theorem greendlinger_of_isConj_relator {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {r : List (α × Bool)} (hr : r ∈ R)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (hconj : IsConj (FreeGroup.mk r) (FreeGroup.mk w)) :
    ∃ t ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: t ∧ t.length < 2 * u.length :=
  greendlinger_of_isConj hR hRne (subset_symmetrization R hr) hw hconj

/-- And keyed to an *inverted* relator, which is the other half of what
`exists_isConj_of_mem_symmetrization` produces. -/
theorem greendlinger_of_isConj_inv {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {r : List (α × Bool)} (hr : r ∈ R)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (hconj : IsConj (FreeGroup.mk r)⁻¹ (FreeGroup.mk w)) :
    ∃ t ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: t ∧ t.length < 2 * u.length := by
  refine greendlinger_of_isConj hR hRne
    (invRev_mem_symmetrization (subset_symmetrization R hr)) hw ?_
  rwa [FreeGroup.inv_mk] at hconj

end SmallCancellationRouter
end GroupApproximation
