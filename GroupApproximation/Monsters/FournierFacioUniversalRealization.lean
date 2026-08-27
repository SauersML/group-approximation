import GroupApproximation.Monsters.RealizationEmbedding

/-!
# Remark `rem:ff-realization`, end to end

`Monsters/FournierFacioRealization` proves the remark's deduction from an
abstract self-embedding `f : P × P →* P`, and `Monsters/RealizationEmbedding`
proves the remark's "in particular" step — that a finitely presented
torsion-free group universal for finitely presented torsion-free groups embeds
its own direct square, because that class is closed under binary products.
What neither file does is *compose* them, which is the last clause of the
audit's repair for this remark.

`rem_ff_realization_universal_endpoint` below is that composition: from the
remark's own hypotheses on `P` — finitely presented, property `(T)`,
torsion-free, and universal — it produces the pair `(α, a)` that
Theorem `thm:kazhdan-clifford` consumes and every conclusion the remark draws
about `E(P, α, a)`.

## What is assumed, and where

Exactly one thing is assumed: `huniv`, the universality of `P`, which is the
theorem of the cited paper.  It is a header hypothesis, in plain Mathlib
vocabulary (`∀ Q, finitely presented → torsion-free → ∃ injection into P`),
not a corpus-defined package that nothing discharges — deliberately, since
such a package is what a later reader picks up and builds on, and since
`scripts/check_non_mf_unconditional.py` reports undischarged corpus packages
as findings.  Everything else in the statement is proved.

Nothing here is badged, and no numbered result of the manuscript depends on
it: the remark states no theorem, carries no `\leanverified` badge, and is
referenced only by a `cf.` pointer from the Questions preamble.  The remark's
own closing sentence — that `E(P, α, a)` contains involutions whatever the
base — is what makes the small-cancellation base buy no torsion-free example,
and it is proved without universality at
`rem_ff_realization_contains_involution_any_base`.
-/

namespace GroupApproximation.Monsters.FournierFacioRealization

open KazhdanCliffordConstruction

universe w

/-- **The remark, from its own hypotheses to its own conclusions.**

Given a finitely presented torsion-free property-`(T)` group `P` that is
universal for finitely presented torsion-free groups, and any nonidentity
`b ∈ P`, there are an injective endomorphism `α` of `P` and an element `a`
outside its image such that the Kazhdan--Clifford extension `E(P, α, a)` is
finitely presented, contains `P`, contains a nontrivial involution, and is not
MF.

`α` and `a` are the remark's own: `α` is `P ≅ P₁ ≤ P` read off the embedded
direct square, and `a` is the image of `b` in the second factor.  The proof
composes `rem_ff_realization_selfSquareEmbedding_of_universal` with the
deductions of `Monsters/FournierFacioRealization`, so the universality input
is used once, at the first step, and nowhere else. -/
theorem rem_ff_realization_universal_endpoint
    {P : Type} [Group P] [Group.IsFinitelyPresented P]
    (hT : HasKazhdanPropertyTComplex.{0, w} P)
    (hP : IsPowerTorsionFree P)
    (huniv : ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ g : Q →* P, Function.Injective g)
    {b : P} (hb : b ≠ 1) :
    ∃ (α : P →* P) (a : P),
      Function.Injective α ∧
        a ∉ Set.range α ∧
        Group.IsFinitelyPresented (Extension α a) ∧
        Function.Injective (iota α a) ∧
        (∃ x : Extension α a, x ≠ 1 ∧ x ^ 2 = 1) ∧
        ¬ IsCDEOperatorMF (Extension α a) := by
  obtain ⟨f, hf⟩ := rem_ff_realization_selfSquareEmbedding_of_universal hP huniv
  exact ⟨selfEmbeddingEndomorphism f, secondFactorElement f b,
    rem_ff_realization_alpha_injective f hf,
    rem_ff_realization_a_notMem_range f hf hb,
    rem_ff_realization_finitelyPresented hT f hf hb,
    rem_ff_realization_base_injective hT f hf hb,
    rem_ff_realization_contains_involution hT f hf hb,
    rem_ff_realization_not_isCDEOperatorMF hT f hf hb⟩

end GroupApproximation.Monsters.FournierFacioRealization
