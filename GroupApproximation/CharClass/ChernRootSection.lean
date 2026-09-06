import GroupApproximation.CharClass.ChernFactorBridge

/-!
# A section of the projective bundle gives a Chern root

The split relation is the hard geometric input.  Its *first* consequence is not:
a section of the projective bundle makes the class it picks out a root of the
Chern polynomial, and that is pure functoriality.

Restricting the defining relation along a section `s` with `s ≫ π = 𝟙` turns
`aeval` into plain `eval`, because the composite of the two pullbacks is the
identity.  So `p(y) = 0` where `y` is the tautological class restricted along the
section — geometrically, the Euler class of the line the section picks out.

At rank one this *pins the convention*: the Chern polynomial of a line bundle is
`X + C e(L)`, with the first Chern class equal to the Euler class rather than
merely congruent to it.  That is the case the whole coefficient indexing is
calibrated against, and it is proved here rather than assumed.

The factor theorem then gives one linear factor.  It does **not** iterate: from
`p(y₁) = p(y₂) = 0` and `p = (X - y₁)q` one gets `(y₂ - y₁) q(y₂) = 0`, and
`y₂ - y₁` is not a non-zero-divisor in a cohomology ring.  Getting all `r`
factors at once is exactly what `SplitRelation` is for.

## Main declarations

* `LerayHirschData.chernPolynomial_isRoot_of_section` — **the root**.
* `LerayHirschData.sub_C_dvd_chernPolynomial_of_section` — one linear factor.
* `LerayHirschData.chern_one_add_root_eq_zero` — **rank one**: the first Chern
  class is the Euler class.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory Polynomial

noncomputable section

namespace LerayHirschData

variable {N P : TopCat.{0}}

/-- **A section gives a root.**  If `s` is a section of the bundle projection and
the tautological class restricts along it to `y`, then `y` is a root of the Chern
polynomial.

The proof is the defining relation pushed along `s`: the composite of the two
pullbacks is the identity, so the `aeval` over the projective bundle becomes an
`eval` over the base. -/
theorem chernPolynomial_isRoot_of_section (D : LerayHirschData N P)
    (s : N ⟶ P) (hs : s ≫ D.proj = 𝟙 N) (y : Hmod2 N 2)
    (hy : TotalH.map s (TotalH.of P 2 D.taut) = TotalH.of N 2 y) :
    D.chernPolynomial.eval (TotalH.of N 2 y) = 0 := by
  have hid : (TotalH.map s).comp (TotalH.map D.proj) = RingHom.id (TotalH N) := by
    refine RingHom.ext fun a => ?_
    show TotalH.map s (TotalH.map D.proj a) = a
    rw [ThomChern.totalMap_comp, hs, ThomChern.totalMap_id]
  have hz : Polynomial.eval₂ (TotalH.map D.proj) (TotalH.of P 2 D.taut)
      D.chernPolynomial = 0 := D.aeval_taut_chernPolynomial
  have h := congrArg (TotalH.map s) hz
  rw [map_zero, Polynomial.hom_eval₂ D.chernPolynomial (TotalH.map D.proj)
    (TotalH.map s) (TotalH.of P 2 D.taut), hy, hid] at h
  exact h

/-- **One linear factor**, by the factor theorem.  This is as far as sections
alone go; see the module docstring for why it does not iterate. -/
theorem sub_C_dvd_chernPolynomial_of_section (D : LerayHirschData N P)
    (s : N ⟶ P) (hs : s ≫ D.proj = 𝟙 N) (y : Hmod2 N 2)
    (hy : TotalH.map s (TotalH.of P 2 D.taut) = TotalH.of N 2 y) :
    (X - C (TotalH.of N 2 y)) ∣ D.chernPolynomial :=
  Polynomial.dvd_iff_isRoot.mpr (D.chernPolynomial_isRoot_of_section s hs y hy)

/-- **Rank one pins the convention.**  For a line bundle the projective bundle is
the base, the tautological class restricts to the Euler class, and the relation
reads `e(L) + γ₁ = 0`.  So `γ₁` is the Euler class, which is what the coefficient
indexing `chern i = coeff (rank - i)` is calibrated against. -/
theorem chern_one_add_root_eq_zero [Nontrivial (TotalH N)] (D : LerayHirschData N P)
    (hr : D.rank = 1) (s : N ⟶ P) (hs : s ≫ D.proj = 𝟙 N) (y : Hmod2 N 2)
    (hy : TotalH.map s (TotalH.of P 2 D.taut) = TotalH.of N 2 y) :
    TotalH.of N 2 y + D.chern 1 = 0 := by
  have hdeg : D.chernPolynomial.natDegree = 1 :=
    (@natDegree_chernPoly (TotalH N) (TotalH P) _ _ D.algebra _ D.powerBasis).trans hr
  have heq : D.chernPolynomial = X + C (D.chernPolynomial.coeff 0) :=
    D.chernPolynomial_monic.eq_X_add_C hdeg
  have hc : D.chern 1 = D.chernPolynomial.coeff 0 := by
    rw [D.chern_eq_coeff (by omega : (1 : ℕ) ≤ D.rank), hr]
  have h := D.chernPolynomial_isRoot_of_section s hs y hy
  rw [heq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at h
  rw [hc]
  exact h

end LerayHirschData

end

end CharClass
end GroupApproximation
