import GroupApproximation.GGT.OsinTheorem54SepAssemble
import GroupApproximation.GGT.OsinTheorem54SepLemma510Right
import GroupApproximation.GGT.GuessingGeodesicsCriterion
import GroupApproximation.GGT.OsinTheorem54SepMultiplicity

/-!
# The assembly, with both halves of Lemma 5.10 discharged

`GGT/OsinTheorem54SepAssemble.lean` removed `hdist` from the binder list of
`sepDataFam_of_binders`; this module removes `hsle` as well, by passing in
`sep_le_dist_enlargedY`.  It sits downstream for the same reason that one does:
`SepInhabit` is imported by everything that proves either half, so neither half
can be folded into it in place.

What that leaves, and what each thing is:

* `h48`, `h49` --- the §4.2 family.  `h48` is Osin's Lemma 4.8, and `h49` is his
  Lemma 4.9 in the GLOBAL form the Λ-sum needs.  These are the geometry.
* `hM`, `hloc` --- the bounded-detour condition of Lemma 5.6 and the local
  finiteness of Lemma 5.8.
* `h511` --- Lemma 5.11, the residue.

Three things that used to be on that list are not on it any more.

Both halves of Lemma 5.10 are theorems of this tree, `dist_le_sep_enlargedY`
and `sep_le_dist_enlargedY`.

Lemma 5.5 is one too.  It was a declared debt until the guessing-geodesics
criterion was proved; `GuessingGeodesicsCriterion.osinLemma55` now supplies it,
so `h55` is gone from the binder list rather than passed through it.

The multiplicity hypothesis is gone as well.  `mult_of_relBall_one` proves it
outright --- an element of two distinct members of the family lies in the
radius-`Dc` ball of either --- so what was once a constraint on the choice of
`Dc` is now a consequence of `1 ≤ Dc`, which the assembly already assumes.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **`SepDataStatementFam` at one `D`, modulo the §4.2 family, Lemma 5.6's and
5.8's conditions, and Lemma 5.11.**

The multiplicity hypothesis is gone too: `mult_of_relBall_one` proves it from
`1 ≤ Dc` alone.

Both halves of Lemma 5.10 are supplied here rather than assumed, and so is
Lemma 5.5: `GuessingGeodesicsCriterion.osinLemma55` proves it outright, so the
`h55` binder is gone from the list.  What Lemma 5.5 was carrying --- the passage
from hyperbolicity of `Γ(G,X ⊔ ℋ)` to hyperbolicity of the enlarged graph ---
is now a theorem of this tree, and `hM` and `hloc` are what remain of that
clause: the bounded-detour condition it consumes and the local finiteness of
Lemma 5.8. -/
theorem sepDataFam_of_binders_of_lemma510 [Fintype Λ] (D : RelGenSet G Λ)
    {Dc : ℕ} (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
    (h49 : ∀ f g h : G, (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ (∑ lam : Λ, sepCard D lam Dc f h)
        + (∑ lam : Λ, sepCard D lam Dc g h) + 2)
    (hemb : D.IsHyperbolicallyEmbedded)
    (hM : ∃ M : ℕ, ∀ b ∈ (enlargedY D hDc hsymm).alphabet.carrier,
      ∀ w : List G, (∀ x ∈ w, x ∈ D.alphabet.carrier) → w.prod = b →
      w.length = wordDist D.alphabet.carrier 1 b →
      ∀ i ≤ w.length,
        wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 (w.take i).prod ≤ M)
    (hloc : ∀ (lam : Λ) (n : ℕ),
      ((enlargedY D hDc hsymm).relBall lam n).Finite)
    (h511 : ∀ m : ℕ, ∃ R N : ℕ, 0 < R ∧ ∀ z : G,
      wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 z = R →
        {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
            wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
              (z⁻¹ * k * z) ≤ m}.Finite ∧
          {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
            wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
              (z⁻¹ * k * z) ≤ m}.ncard ≤ N) :
    ∃ S : SepDataFam D, S.AcylindricalCore :=
  sepDataFam_of_binders_of_dist D hDc hsymm h48 h49 osinLemma55 hemb hM hloc
    (fun f g => sep_le_dist_enlargedY D hDc hsymm h48
      (mult_of_relBall_one D hDc) h49 f g) h511

end OsinEnlargement
end GGT
end GroupApproximation
