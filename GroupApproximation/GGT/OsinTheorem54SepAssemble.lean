import GroupApproximation.GGT.OsinTheorem54SepDistLeSep

/-!
# The assembly, with Lemma 5.10's left half discharged

`sepDataFam_of_binders` in `GGT/OsinTheorem54SepInhabit.lean` carries `hdist`
as a binder.  It cannot discharge it in place: `SepDistBase` imports
`SepInhabit` for `enlargedY`, and the whole `SepDist*` chain sits above it, so
`SepInhabit` importing `dist_le_sep_enlargedY` would close a cycle.

The fix is to instantiate downstream rather than to move anything.  This module
sits above both and passes the proved half in, so the binder list here is one
shorter and nothing upstream moves.

`h48` is genuinely used here — the induction inside `dist_le_sep_enlargedY`
consumes Lemma 4.8's penetration half through the enumeration bridge — which is
why it is named `h48` below and `_h48` upstream, where it really is unused.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **`SepDataStatementFam` at one `D`, modulo five binders.**

`hdist` is gone, discharged by `dist_le_sep_enlargedY`.  What remains: `h48` and
`h49` (the §4.2 family), `h55` with `hM` and `hloc` (Lemma 5.5 and its two
companions), `hsle` (Lemma 5.10's right half, provable and not a leaf), and
`h511` (Lemma 5.11). -/
theorem sepDataFam_of_binders_of_dist [Fintype Λ] (D : RelGenSet G Λ) {Dc : ℕ}
    (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
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
    (hsle : ∀ f g : G, (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ 3 * wordDist (enlargedY D hDc hsymm).alphabet.carrier f g)
    (h511 : ∀ m : ℕ, ∃ R N : ℕ, 0 < R ∧ ∀ z : G,
      wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 z = R →
        {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
            wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
              (z⁻¹ * k * z) ≤ m}.Finite ∧
          {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
            wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
              (z⁻¹ * k * z) ≤ m}.ncard ≤ N) :
    ∃ S : SepDataFam D, S.AcylindricalCore :=
  sepDataFam_of_binders D hDc hsymm h48 h49 h55 hemb hM hloc
    (dist_le_sep_enlargedY D hDc hsymm h48) hsle h511

end OsinEnlargement
end GGT
end GroupApproximation
