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

This file is the word-level half of it.  The classical proof is in two steps:
an element of finite order is conjugate into a factor, and a factor is
torsion-free by hypothesis.  The second step is `eq_one_of_pow_eq_one_of`.
The first splits again: an element whose word is *cyclically* reduced ---
nonempty, with first and last letters in different summands --- has all its
powers reduced and nonempty, hence nontrivial, because Mathlib's
`Monoid.PushoutI.Reduced.eq_empty_of_mem_range` says a reduced nonempty word is
never in the base.

What is left after this file is the cyclic reduction itself: that every element
is conjugate either into a factor or to one with a cyclically reduced word.
-/

namespace GroupApproximation
namespace Higman
namespace AmalgamTorsion

open Monoid Monoid.CoprodI Monoid.PushoutI

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} {H : Type*}
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

omit [DecidableEq ι] in
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

end AmalgamTorsion
end Higman
end GroupApproximation
