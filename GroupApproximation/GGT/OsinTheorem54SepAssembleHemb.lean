import GroupApproximation.GGT.OsinTheorem54SepAssembleFull
import GroupApproximation.GGT.OsinTheorem54SepFourPointBridge

/-!
# The assembly with the §4.2 family folded in

`sepDataFam_of_binders_of_lemma510` takes Osin's Lemmas 4.8 and 4.9 as binders.
They are theorems now --- `lemmaFourEight_of_bound`, `lemmaFourNine_of_bound`,
and, over clause (a) of hyperbolic embedding,
`exists_lemmaFourEight_and_lemmaFourNine_of_isHyperbolicallyEmbedded` --- so
this module states the assembly without them.

Nothing is renamed and nothing loses a binder: the theorem below is ADDITIVE,
and `sepDataFam_of_binders_of_lemma510` keeps the shape every other lane is
already calling.  What changes is only what a caller has to supply.

## Why the constant comes first

`Dc` cannot be fixed before `C`.  The §4.2 bound produces `C`, and Lemma 4.5 ---
whose isolation step is the one place a constant is spent in this whole chain
--- needs `4C ≤ Dc`.  So the statement quantifies `C` first, then `Dc` past the
threshold, and only then the three remaining conditions, whose statements
mention `enlargedY D hDc hsymm` and therefore cannot even be written before `Dc`
and its `1 ≤ Dc` are in hand.

That ordering is Osin's own: Remark 4.4 chooses `D` with `C` already known.

## What is left

`hM` (the bounded-detour condition of Lemma 5.6), `hloc` (local finiteness,
Lemma 5.8) and `h511` (acylindricity, Lemma 5.11).  Hyperbolic embedding and a
symmetric base carry everything else.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **`SepDataStatementFam` from hyperbolic embedding, Lemma 5.6's condition,
Lemma 5.8's and Lemma 5.11.**  The §4.2 family is discharged rather than
assumed. -/
theorem exists_sepDataFam_of_hemb [Fintype Λ] (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (hemb : D.IsHyperbolicallyEmbedded) :
    ∃ C : ℕ, 0 < C ∧ ∀ (Dc : ℕ) (hDc : 1 ≤ Dc), C * 4 ≤ Dc →
      (∃ M : ℕ, ∀ b ∈ (enlargedY D hDc hsymm).alphabet.carrier,
        ∀ w : List G, (∀ x ∈ w, x ∈ D.alphabet.carrier) → w.prod = b →
        w.length = wordDist D.alphabet.carrier 1 b →
        ∀ i ≤ w.length,
          wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 (w.take i).prod ≤ M) →
      (∀ (lam : Λ) (n : ℕ), ((enlargedY D hDc hsymm).relBall lam n).Finite) →
      (∀ m : ℕ, ∃ R N : ℕ, 0 < R ∧ ∀ z : G,
        wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 z = R →
          {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
              wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
                (z⁻¹ * k * z) ≤ m}.Finite ∧
            {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
              wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
                (z⁻¹ * k * z) ≤ m}.ncard ≤ N) →
      ∃ S : SepDataFam D, S.AcylindricalCore := by
  obtain ⟨C, hCpos, hboth⟩ :=
    exists_lemmaFourEight_and_lemmaFourNine_of_isHyperbolicallyEmbedded D hsymm hemb
  refine ⟨C, hCpos, fun Dc hDc hthr hM hloc h511 => ?_⟩
  obtain ⟨h48, h49⟩ := hboth Dc hthr
  exact sepDataFam_of_binders_of_lemma510 D hDc hsymm h48 h49 hemb hM hloc h511

end OsinEnlargement
end GGT
end GroupApproximation
