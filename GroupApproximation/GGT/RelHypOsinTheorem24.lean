import GroupApproximation.GGT.RelHypDefinition
import GroupApproximation.Sofic.GreendlingerRelativeTransfer

/-!
# Osin's Theorem 2.4, and the small-cancellation quotient of Fournier-Facio's
Proposition 2.3

D. Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems*, Ann. of Math. 172 (2010) 1--39, Theorem 2.4; and
Fournier-Facio et al., Proposition 2.3, which applies it to the relatively
hyperbolic pair `(U ∗ H, U)`.

## What Osin's Theorem 2.4 says, and where its clauses already live

Let `G` be hyperbolic relative to `{H_λ}` with finite relative generating set
`X`.  Osin fixes `μ > 0` and `c ≥ 0`, and then for every `λ ∈ (0,1]` and
`ε ≥ 0` produces `ρ > 0` such that every symmetrized set `R` of words over
`X ⊔ ℋ` satisfying the relative small-cancellation condition
`C(ε, μ, λ, c, ρ)` has, in `G/⟪R⟫`:

1. the restriction of `G → G/⟪R⟫` to each `H_λ` is **injective**;
2. `G/⟪R⟫` is hyperbolic relative to the images of the `H_λ`;
3.--(4) statements about `⟪R⟫` as a free product of conjugates;
5. every element of finite order in `G/⟪R⟫` is the image of an element of the
   same order in `G` -- so a torsion-free `G` has a **torsion-free** quotient.

Clauses (1) and (5) are the two the Fournier-Facio paragraph consumes, and
this repository already has them in the free-product model, with pieces
measured in `Monoid.CoprodI` syllables: `Sofic/OsinRelativeSmallCancellation`
proves that the length form of the Greendlinger conclusion gives the embedding
clause and that the torsion classification gives torsion-freeness, and
`Sofic/GreendlingerRelativeTransfer` cuts what remains down to two named
predicates on the relator family and assembles the four conclusions in
`osin_conclusion_of_metric`.

So Theorem 2.4 is **not** restated here as a fresh monolithic citation.  It is
stated as exactly the universal closure of those two repository leaves --

    OsinTheorem24 = ∀ R lam, RelativeGreendlingerLeaf R lam
                             ∧ RelativeTorsionLeaf R lam

-- which is faithful (each leaf carries Osin's own design hypotheses:
symmetrization, cyclic reducedness, the metric condition with fragment slack,
and, for the torsion leaf, no relator a proper power), is checkable against
the definitions rather than against a docstring, and spends the ~800 lines of
proved repository content instead of duplicating them.  The mathematics still
open behind it is one van Kampen count, described at length in the docstrings
of the two modules above; nothing here reopens it.

## What Proposition 2.3 adds, and why it is a second input

Osin's theorem is about relator families that satisfy the small-cancellation
condition; it does not say that a *useful* such family exists.  Fournier-Facio's
Proposition 2.3 supplies the family: over `G = U ∗ H` with peripheral `U`, take
one relator `u_k w_k` for each generator `u_k` of `U`, where `w_k` is a long
word in `H` chosen in general position -- Osin's §4 provides the general
position, in a non-elementary relatively hyperbolic group, for any prescribed
parameters.  In the quotient every `u_k` becomes equal to `w_k⁻¹`, an element
of the image of `H`, so the image of `H` is everything.

`OsinRelatorDesign` is that clause, stated with the design certificates the
repository's transfer layer actually consumes (finite, symmetrized, cyclically
reduced, at least 42 syllables, `C'(1/7)`, no proper powers) and with the one
extra property that the relator *shape* buys: each generator of `U` is
identified with an element of the image of `H`.  Non-elementarity and relative
hyperbolicity of `(U ∗ H, U)` are hypotheses of it, so the geometric input is
visible in the type.

## What is proved here

`exists_smallCancellationQuotient`.  Given the two named inputs above and the
geometric statement of `GGT/RelHypDefinition.lean`, the quotient
`P = (U ∗ H)/⟪R⟫` is a finitely presented torsion-free group in which `U`
embeds and onto which `H` surjects.  Four clauses, and each is a step this
module proves rather than imports:

* `U ↪ P` is `osin_conclusion_of_metric`'s embedding clause at index `false`;
* `P` torsion-free is its fourth conclusion, over the torsion-free factors;
* `P` finitely presented is `Group.IsFinitelyPresented.quotient` against
  `CoprodIFinitePresentation.instCoprodI`, the relator family being finite --
  Mathlib has the free product and the quotient step, this repository has the
  indexed free product;
* `H ↠ P` is `rightFactorHom_surjective`: the image of `H` is a subgroup
  containing the image of a generating set of `U`, hence containing the image
  of `U`, and the two factor images generate.  This is the step the relator
  shape is designed for, and it is the only one that is not read off a
  conclusion list.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open OsinSmallCancellation GreendlingerRelativeTransfer

/-! ## 1.  Osin's Theorem 2.4, clauses (1) and (5) -/

/-- **Osin, Theorem 2.4(1) and 2.4(5)**, in the free-product model with pieces
measured in syllables: for every relator family and every constant, the
relative Greendlinger lemma and the relative torsion classification hold.

Each conjunct is the corresponding leaf of
`Sofic/GreendlingerRelativeTransfer`, which carries Osin's design hypotheses in
its own binders -- symmetrization, cyclic reducedness, fragment slack, the
metric condition, and (for the torsion clause) no relator a proper power -- so
this `Prop` is the honest universal closure of the two open leaves and not a
weakening of them. -/
def OsinTheorem24 : Prop :=
  ∀ (ι : Type) (_ : DecidableEq ι) (G : ι → Type) (_ : ∀ i, Group (G i))
    (_ : ∀ i, DecidableEq (G i)) (R : Set (Word G)) (lam : ℚ),
      RelativeGreendlingerLeaf R lam ∧ RelativeTorsionLeaf R lam

/-! ## 2.  The two factor images generate the quotient -/

/-- **The image of `H` fills the quotient**, once every generator of `U` has
been identified with an element of it.

The image of `H` is a subgroup, so it contains the image of the subgroup of `U`
generated by `S`; that subgroup is all of `U`, and the two factor images
generate `U ∗ H`, hence the quotient. -/
theorem rightFactorHom_surjective {U H : Type} [Group U] [Group H]
    (K : Subgroup (CoprodI (pairFamily U H))) [K.Normal] (S : Finset U)
    (hS : Subgroup.closure (S : Set U) = ⊤)
    (hSmem : ∀ u ∈ S, ∃ h : H, leftFactorHom K u = rightFactorHom K h) :
    Function.Surjective (rightFactorHom K) := by
  have hall : ∀ u : U, leftFactorHom K u ∈ (rightFactorHom K).range := by
    have hgen : (S : Set U) ⊆
        ((Subgroup.comap (leftFactorHom K) (rightFactorHom K).range :
          Subgroup U) : Set U) := by
      intro u hu
      obtain ⟨h, hh⟩ := hSmem u (Finset.mem_coe.mp hu)
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.mem_range]
      exact ⟨h, hh.symm⟩
    have hle := (Subgroup.closure_le _).mpr hgen
    rw [hS] at hle
    intro u
    have hmem := hle (Subgroup.mem_top u)
    rwa [Subgroup.mem_comap] at hmem
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  rintro q -
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K q
  induction g using CoprodI.induction_on with
  | one =>
      rw [map_one]
      exact one_mem _
  | of b x =>
      cases b
      · exact hall x
      · exact ⟨x, rfl⟩
  | mul y z hy hz =>
      rw [map_mul]
      exact mul_mem hy hz

/-! ## 3.  The relator design of Proposition 2.3 -/

/-- **Fournier-Facio, Proposition 2.3**: the choice of relators, and Osin's
§4 general position behind it.

Over the relatively hyperbolic pair `(U ∗ H, U)` with `H` non-elementary
hyperbolic, there is a finite symmetrized family of long cyclically reduced
relators, no one of them a proper power, satisfying the metric condition, whose
*shape* identifies every generator of `U` with an element of the image of `H`.

The last clause is the one that makes the quotient a quotient of `H`; the
others are exactly the design certificates
`GreendlingerRelativeTransfer.osin_conclusion_of_metric` consumes, at its
concrete pair `(1/7, 42)`.  The pair is free: any `lam < 1/6` with relators of
at least `1/(1/6 - lam)` syllables does as well
(`GreendlingerRelativeTransfer.fragmentSlack_of_le_seventh`). -/
def OsinRelatorDesign : Prop :=
  ∀ (U H : Type) (_ : Group U) (_ : Group H)
    (_ : ∀ b, DecidableEq (pairFamily U H b)),
    Group.IsFinitelyPresented U → IsPowerTorsionFree U →
      Infinite H → Group.IsFinitelyPresented H → IsPowerTorsionFree H →
        IsNonElementaryHyperbolic H →
          IsRelativelyHyperbolic (CoprodI (pairFamily U H))
              (fun _ : Unit => freeProductPeripheral U H) →
            ∃ R : Set (Word (pairFamily U H)),
              R.Finite ∧
                Symmetrized R ∧
                (∀ r ∈ R, IsCyclicallyReduced r) ∧
                (∀ r ∈ R, 42 ≤ wlen r) ∧
                MetricSmallCancellation R (1 / 7) ∧
                NoProperPower R ∧
                ∃ S : Finset U, Subgroup.closure (S : Set U) = ⊤ ∧
                  ∀ u ∈ S, ∃ h : H,
                    leftFactorHom (relatorSubgroup R) u
                      = rightFactorHom (relatorSubgroup R) h

/-! ## 4.  The quotient -/

/-- **The small-cancellation quotient of Fournier-Facio's Proposition 2.3.**

From Osin's Theorem 2.4, the relator design, and the relative hyperbolicity of
the free product: a finitely presented torsion-free group `P` in which `U`
embeds and onto which `H` surjects.

Every hypothesis of `OsinRelatorDesign` is discharged here from the hypotheses
of the theorem, so the only literature debt of the conclusion is the three
named `Prop`s in the binder list. -/
theorem exists_smallCancellationQuotient
    (hOsin : OsinTheorem24) (hDesign : OsinRelatorDesign)
    (hRelHyp : FreeProductRelativelyHyperbolicStatement)
    (U H : Type) [Group U] [Group H]
    (hUfp : Group.IsFinitelyPresented U) (hUtf : IsPowerTorsionFree U)
    (hHinf : Infinite H) (hHfp : Group.IsFinitelyPresented H)
    (hHtf : IsPowerTorsionFree H) (hHne : IsNonElementaryHyperbolic H) :
    ∃ (P : Type) (_ : Group P),
      Group.IsFinitelyPresented P ∧ IsPowerTorsionFree P ∧
        (∃ p : H →* P, Function.Surjective p) ∧
        (∃ e : U →* P, Function.Injective e) := by
  haveI := hUfp
  haveI := hHfp
  haveI hdec : ∀ b, DecidableEq (pairFamily U H b) := pairFamilyDecEq U H
  have hrh : IsRelativelyHyperbolic (CoprodI (pairFamily U H))
      (fun _ : Unit => freeProductPeripheral U H) :=
    hRelHyp U H inferInstance inferInstance hHne.1
  obtain ⟨R, hRfin, hsym, hcyc, hlong, hmetric, hnpp, S, hSclosure, hSmem⟩ :=
    hDesign U H inferInstance inferInstance hdec hUfp hUtf hHinf hHfp hHtf hHne
      hrh
  have hfree : ∀ b, IsPowerTorsionFree (pairFamily U H b) :=
    isPowerTorsionFree_pairFamily hUtf hHtf
  obtain ⟨-, -, hinj, hPtf⟩ :=
    osin_conclusion_of_metric
      (hOsin Bool inferInstance (pairFamily U H) inferInstance hdec R (1 / 7)).1
      (hOsin Bool inferInstance (pairFamily U H) inferInstance hdec R (1 / 7)).2
      hsym hcyc hlong hmetric hnpp hfree
  refine ⟨CoprodI (pairFamily U H) ⧸ relatorSubgroup R, inferInstance, ?_, hPtf,
    ⟨rightFactorHom (relatorSubgroup R), ?_⟩,
    ⟨leftFactorHom (relatorSubgroup R), ?_⟩⟩
  · exact Group.IsFinitelyPresented.quotient (relatorSubgroup R)
      ⟨Word.prod '' R, hRfin.image Word.prod, rfl⟩
  · exact rightFactorHom_surjective (relatorSubgroup R) S hSclosure hSmem
  · exact hinj false

end RelHyp
end GGT
end GroupApproximation
