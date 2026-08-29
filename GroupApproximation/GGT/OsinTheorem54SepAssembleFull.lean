import GroupApproximation.GGT.OsinTheorem54SepAssemble
import GroupApproximation.GGT.OsinTheorem54SepLemma510Right

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
* `hmult` --- the multiplicity hypothesis, which is a constraint on the choice
  of `Dc` and not a new geometric leaf; its provenance is recorded at
  `GGT/OsinTheorem54SepLetterMult.lean`.
* `h55`, `hM`, `hloc` --- Lemma 5.5 (a declared debt), the bounded-detour
  condition of Lemma 5.6, and the local finiteness of Lemma 5.8.
* `h511` --- Lemma 5.11, the residue.

Lemma 5.10 does not appear.  Both halves are now theorems of this tree:
`dist_le_sep_enlargedY` and `sep_le_dist_enlargedY`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **`SepDataStatementFam` at one `D`, modulo the §4.2 family, Lemma 5.5 with
its two companions, and Lemma 5.11.**

Both halves of Lemma 5.10 are supplied here rather than assumed. -/
theorem sepDataFam_of_binders_of_lemma510 [Fintype Λ] (D : RelGenSet G Λ)
    {Dc : ℕ} (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
    (hmult : ∀ lam mu : Λ, lam ≠ mu → ∀ x : G, x ∈ D.fam lam → x ∈ D.fam mu →
      x ∈ D.relBall lam Dc ∨ x ∈ D.relBall mu Dc)
    (h49 : ∀ f g h : G, (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ (∑ lam : Λ, sepCard D lam Dc f h)
        + (∑ lam : Λ, sepCard D lam Dc g h) + 2)
    (h55 : OsinLemma55.{u}) (hemb : D.IsHyperbolicallyEmbedded)
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
  sepDataFam_of_binders_of_dist D hDc hsymm h48 h49 h55 hemb hM hloc
    (fun f g => sep_le_dist_enlargedY D hDc hsymm h48 hmult h49 f g) h511

end OsinEnlargement
end GGT
end GroupApproximation
