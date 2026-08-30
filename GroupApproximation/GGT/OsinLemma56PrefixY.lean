import GroupApproximation.GGT.OsinTheorem54SepDistBase

/-!
# Osin's Lemma 5.6, on one named hypothesis

The `hM` binder of `OsinTheorem54SepAssembleFull.sepDataFam_of_binders_of_lemma510`
is the bounded-detour condition: every prefix of an old geodesic to a letter of
the enlarged alphabet stays within `M` of the basepoint in the *enlarged*
metric.  It is verbatim the `M`-hypothesis of `OsinLemma55`, which is why the
two binders sit together --- one feeds the other.

This module discharges it from a single named statement,
`SepPrefixInheritance`, and nothing else.

## What the hypothesis says, and why it is not proved here

Osin's proof of 5.6 is a per-vertex contradiction: if some coset separated `1`
from a vertex `v` of the geodesic, the geodesic `q` realising that separation,
spliced onto the remainder `p₂`, would separate `1` from the endpoint --- which
lies in `Y`.  The splice `q p₂` is again geodesic, its length being the sum
through a vertex of a geodesic, so the witnessing component of `q` survives into
it with its span untouched and essentiality passes by identity.

The one thing to check is that the splice cannot *extend* the witnessing run,
which would change the span.  It cannot, and the reason is worth recording
because it is invisible from the bookkeeping: **a geodesic word has single-letter
components.**  Two adjacent letters of one index multiply --- the family is a
subgroup --- so replacing them by their product spells the same element one
letter shorter.  A geodesic word therefore never carries two adjacent letters of
one index, every maximal run is a single letter, and since `q p₂` is itself
geodesic the letter following the run is not of the run's index.

So the statement below is true under the definitions as they stand.  It is a
hypothesis here only for want of the no-adjacent-letters lemma, which belongs to
the `OsinPenetration` vocabulary rather than to this module.

An earlier reading of this seam --- that the definition here diverges from
Osin's by asking for a maximal component where he asks for a subpath --- was
wrong on both halves: his Definition 4.3 is component-based verbatim, and the
configuration the divergence was invoked to explain does not arise on geodesics
at all.  It is recorded because the arithmetic that appeared to permit it is
sound as arithmetic: `s ∉ relBall lam Dc` together with `s * t ∈ relBall lam Dc`
is consistent for a left-invariant `d_lam`, and no depth estimate excludes it.
The sharpest that route yields is that such a run would span at most `Dc`
letters, `d_lam` dominating the `X ⊔ ℋ` word metric on a geodesic.  What
excludes the configuration is the shape of geodesic words, not the size of the
constants.

## The constant is `1` here, and Osin states `2`

Given the inheritance, the prefix lies in `Y`, hence is a single letter of the
enlarged alphabet, and `wordDist_enlargedY_le_one` reads the bound off.  What
this module proves is `M = 1` **relative to the hypothesis it assumes**, and a
reader comparing constants against the paper should not read it as a claim about
the printed lemma.

Osin states 5.6 with `2`.  Since the inheritance holds outright rather than only
where a seam is absent, the argument recorded above yields `1`, so his `2` either
carries slack or answers to something in his statement that the `hM` binder does
not see.  Nothing here settles which.  An earlier reading of that `2` as the
exact price of the seam is withdrawn: the seam it priced does not arise.

## The family case is not the same case

A letter of `⋃ H` need not lie in `Y`: the one-letter geodesic to a deep
element of `H_lam` essentially penetrates its own coset.  That is exactly why
the enlarged alphabet is `Y ∪ ⋃ H` rather than `Y`, and why the proof below
splits.  In that branch the old geodesic has length at most one and there is
nothing to inherit.

## What it costs

`h48` is **not** used.  The reduction runs through
`wordDist_enlargedY_le_one`, which is unconditional, rather than through the
counting form; so `hM` is discharged on `SepPrefixInheritance` alone, with
strictly fewer hypotheses than its sibling binders carry.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Subgeodesic inheritance of the empty separating set.**

If nothing separates `1` from `y`, then nothing separates `1` from any vertex of
an old geodesic to `y`.  True under the definitions as they stand --- see the
module header --- and carried as a hypothesis only until the
no-adjacent-letters lemma it rests on is available. -/
def SepPrefixInheritance (D : RelGenSet G Λ) (Dc : ℕ) : Prop :=
  ∀ y : G, (∀ lam : Λ, sepSet D lam Dc 1 y = ∅) →
    ∀ w : List G, (∀ x ∈ w, x ∈ D.alphabet.carrier) → w.prod = y →
      w.length = wordDist D.alphabet.carrier 1 y →
        ∀ i ≤ w.length, ∀ mu : Λ, sepSet D mu Dc 1 (w.take i).prod = ∅

/-- **Osin's Lemma 5.6**, on the inheritance hypothesis: the bounded-detour
condition holds with `M = 1`.

This is the `hM` binder of `sepDataFam_of_binders_of_lemma510`, discharged
modulo `SepPrefixInheritance`. -/
theorem exists_boundedDetour_of_sepPrefixInheritance (D : RelGenSet G Λ)
    {Dc : ℕ} (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hinh : SepPrefixInheritance D Dc) :
    ∃ M : ℕ, ∀ b ∈ (enlargedY D hDc hsymm).alphabet.carrier,
      ∀ w : List G, (∀ x ∈ w, x ∈ D.alphabet.carrier) → w.prod = b →
      w.length = wordDist D.alphabet.carrier 1 b →
      ∀ i ≤ w.length,
        wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
          (w.take i).prod ≤ M := by
  refine ⟨1, ?_⟩
  intro b hb w hlet hprod hlen i hi
  rcases hb with hbY | hbH
  · -- `b` lies in `Y`: every prefix does too, and a `Y`-letter is one step away
    exact wordDist_enlargedY_le_one D hDc hsymm
      (fun mu => hinh b hbY w hlet hprod hlen i hi mu)
  · -- `b` is a letter of the family: the old geodesic has length at most one
    have hbA : b ∈ D.alphabet.carrier := Set.mem_union_right _ hbH
    have hb1 : wordNorm D.alphabet.carrier b ≤ 1 :=
      wordNorm_le_one_of_mem hbA
    have hw1 : w.length ≤ 1 := by
      rw [hlen, wordDist_one_left]
      exact hb1
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [List.take_zero, List.prod_nil]
      have h := wordDist_self (enlargedY D hDc hsymm).alphabet.carrier (1 : G)
      omega
    · have hiw : i = w.length := by omega
      subst hiw
      rw [List.take_length, hprod]
      show wordNorm (enlargedY D hDc hsymm).alphabet.carrier
        ((1 : G)⁻¹ * b) ≤ 1
      rw [inv_one, one_mul]
      exact wordNorm_le_one_of_mem (Set.mem_union_right _ hbH)

end OsinEnlargement
end GGT
end GroupApproximation
