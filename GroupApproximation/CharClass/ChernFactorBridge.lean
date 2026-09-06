import GroupApproximation.CharClass.ChernSplittingInjective
import GroupApproximation.CharClass.ThomChernBasis

/-!
# The factorisation, from the split relation upstairs

Three places want the same hypothesis — `ChernWhitneyFlag`'s
`hasSplitting_of_splitPoly`, `ChernSplittingInjective`'s
`hasSplitting_of_splitPoly_injective`, and `LemmaTwoStepDLix`'s `hslice` — namely
that after pullback the Chern polynomial factors into linear factors.  This file
reduces all three to one named statement about the *geometry* and nothing else.

That statement is `SplitRelation`: on the pulled-back projective bundle the
tautological class satisfies `∏_l (ξ + e(L_l)) = 0`.  Everything between it and
the factorisation is algebra already on `origin/main`: uniqueness of the Chern
polynomial gives the factorisation upstairs, and naturality identifies it with
the image of the one downstairs.

The two compatibility hypotheses are exactly what a pullback square supplies:
the square of spaces commutes, and the tautological class of the pulled-back
bundle is the pullback of the tautological class.  Neither mentions a bundle.

Nothing here constructs a `LerayHirschData`; both are inputs, as they are
everywhere else in this layer.

## Main declarations

* `LerayHirschData.SplitRelation` — **the one geometric input**, named.
* `LerayHirschData.aeval_taut_map` — the pulled-back relation still kills the
  tautological class upstairs.
* `LerayHirschData.splitPoly_of_splitRelation` — **the factorisation**, in the
  shape the three consumers take as a hypothesis.
* `hasSplitting_of_splitRelation` — the same, carried all the way to `cc-wu`'s
  `HasSplitting`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory Polynomial

noncomputable section

namespace LerayHirschData

variable {N F P P' : TopCat.{0}}

/-- **The one geometric input.**  On the projectivisation of a bundle that splits
into lines, the tautological class satisfies the split relation.

Written with `TotalH.map D'.proj` rather than `algebraMap` so that the statement
mentions no algebra instance; the two are the same map, because the algebra is
`RingHom.toAlgebra` of exactly that pullback. -/
def SplitRelation (D' : LerayHirschData F P') (r : ℕ) (root : ℕ → Hmod2 F 2) : Prop :=
  ∏ l ∈ Finset.range r,
      (TotalH.of P' 2 D'.taut + TotalH.map D'.proj (TotalH.of F 2 (root l))) = 0

/-- **The pulled-back relation still holds upstairs.**  This is the hypothesis
`chernPoly_map` needs, and it follows from the commuting square and the
compatibility of tautological classes alone: pushing `eval₂` through both turns
it into `TotalH.map q` applied to the relation downstairs. -/
theorem aeval_taut_map (D : LerayHirschData N P) (D' : LerayHirschData F P')
    (proj : F ⟶ N) (q : P' ⟶ P)
    (hsq : D'.proj ≫ proj = q ≫ D.proj)
    (htaut : TotalH.of P' 2 D'.taut = TotalH.map q (TotalH.of P 2 D.taut)) :
    @Polynomial.aeval (TotalH F) (TotalH P') _ _ D'.algebra
        (TotalH.of P' 2 D'.taut) (D.chernPolynomial.map (TotalH.map proj)) = 0 := by
  have hkey : (TotalH.map D'.proj).comp (TotalH.map proj)
      = (TotalH.map q).comp (TotalH.map D.proj) := by
    refine RingHom.ext fun a => ?_
    show TotalH.map D'.proj (TotalH.map proj a) = TotalH.map q (TotalH.map D.proj a)
    rw [ThomChern.totalMap_comp, ThomChern.totalMap_comp, hsq]
  have hz : Polynomial.eval₂ (TotalH.map D.proj) (TotalH.of P 2 D.taut)
      D.chernPolynomial = 0 := D.aeval_taut_chernPolynomial
  show Polynomial.eval₂ (TotalH.map D'.proj) (TotalH.of P' 2 D'.taut)
      (D.chernPolynomial.map (TotalH.map proj)) = 0
  rw [Polynomial.eval₂_map, hkey, htaut,
    ← Polynomial.hom_eval₂ D.chernPolynomial (TotalH.map D.proj) (TotalH.map q)
      (TotalH.of P 2 D.taut), hz, map_zero]

/-- **The factorisation.**  From the split relation on the pulled-back projective
bundle, the Chern polynomial factors after pullback.

Two named steps: `chernPoly_eq_prod_of_root` gives the factorisation of the
upstairs Chern polynomial, and `chernPoly_map` identifies that with the image of
the downstairs one. -/
theorem splitPoly_of_splitRelation [Nontrivial (TotalH N)] [Nontrivial (TotalH F)]
    (D : LerayHirschData N P) (D' : LerayHirschData F P')
    (proj : F ⟶ N) (q : P' ⟶ P)
    (hsq : D'.proj ≫ proj = q ≫ D.proj)
    (htaut : TotalH.of P' 2 D'.taut = TotalH.map q (TotalH.of P 2 D.taut))
    (r : ℕ) (hr : D.rank = r) (hr' : D'.rank = r)
    (root : ℕ → Hmod2 F 2) (hrel : D'.SplitRelation r root) :
    D.chernPolynomial.map (TotalH.map proj)
      = ∏ l ∈ Finset.range r, (X + C (TotalH.of F 2 (root l))) := by
  have h1 : D'.chernPolynomial
      = ∏ l ∈ Finset.range r, (X + C (TotalH.of F 2 (root l))) :=
    @chernPoly_eq_prod_of_root (TotalH F) (TotalH P') _ _ D'.algebra _ ℕ
      D'.powerBasis (Finset.range r) (fun l => TotalH.of F 2 (root l))
      (by rw [Finset.card_range]; exact hr'.symm) hrel
  have h2 : D'.chernPolynomial = D.chernPolynomial.map (TotalH.map proj) :=
    @chernPoly_map (TotalH N) (TotalH F) (TotalH P) (TotalH P') _ _ D.algebra
      _ _ D'.algebra _ _ D.powerBasis D'.powerBasis (TotalH.map proj)
      (hr'.trans hr.symm) (aeval_taut_map D D' proj q hsq htaut)
  rw [← h2, h1]

end LerayHirschData

/-- **`cc-wu`'s splitting data from the split relation.**  The composite of this
file's bridge with `ChernWhitneyFlag`'s Whitney statement; after it the only open
obligation in the whole chain is `SplitRelation`. -/
theorem hasSplitting_of_splitRelation {N F P P' : TopCat.{0}}
    [Nontrivial (TotalH N)] [Nontrivial (TotalH F)]
    (D : LerayHirschData N P) (D' : LerayHirschData F P')
    (proj : F ⟶ N) (q : P' ⟶ P)
    (hsq : D'.proj ≫ proj = q ≫ D.proj)
    (htaut : TotalH.of P' 2 D'.taut = TotalH.map q (TotalH.of P 2 D.taut))
    (hinj : Function.Injective (TotalH.map proj))
    (r : ℕ) (hr : D.rank = r) (hr' : D'.rank = r)
    (root : ℕ → Hmod2 F 2)
    (hroot : ∀ l : ℕ, ∃ (d : ℕ) (g : F ⟶ CPtop d) (h : Hmod2 (CPtop d) 2),
      root l = pull g 2 h)
    (hrel : D'.SplitRelation r root) :
    Wu.HasSplitting N D.chern :=
  LH.hasSplitting_of_splitPoly_injective D proj hinj r hr root hroot
    (D.splitPoly_of_splitRelation D' proj q hsq htaut r hr hr' root hrel)

end

end CharClass
end GroupApproximation
