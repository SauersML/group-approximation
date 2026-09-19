import GroupApproximation.Analysis.ShulmanFillNormingEllTwoTheorem10

/-!
# Theorem 4 at the printed models, as one package

`Analysis/ShulmanFillNormingExistentialLiftTwoLeg` contains an obsolete
two-representation strengthening of Shulman's one-leg Theorem 4.  Even that
binder is too weak to drive Theorem 10: it produces two lifts into one model
and says nothing relating them on `C`, whereas
`ShulmanFill.isMFAlgebra_amalgam_of_doubleLR` needs
`∀ c, ‖φ₁_t (k c) - φ₂_t (k c)‖ → 0`.  That agreement is Shulman's Lemma 9 — in
the paper it is what the Halmos dilation and Pedersen's commutator inequality
are for.  This agreement is not a conclusion of Theorem 4; it is produced only
for the stabilized flip-conjugate pair in the proof of Theorem 10.

`Theorem4PrintedPairStatement` below states the package as one Prop, and pins
the coefficient algebras to the printed family `EllTwoCoefficient n = B(ℂ^{n+1})`
— Shulman's `M_{n+1}`, the family his `𝒟 ⊂ ∏ₙ Mₙ` is built from.  Two things
follow at once.

* **No `HasMFEmbedding` clause is needed.**  The coefficients are matrix
  algebras, so the MF-ness of the doubled `𝒟` is not an assumption but a
  theorem: `Analysis/ShulmanFillNormingEllTwoTheorem10` discharges it from
  `hasMFEmbedding_doubledEllTwoStarStrong`.  At a general coefficient family it
  could not be, and the reason is recorded in the header of
  `Analysis/ShulmanFillNormingProductMF`: a general product permanence
  statement for `HasMFEmbedding` is not elementary.
* **No existential over types is needed**, so the statement carries no `letI`
  and no instance binders inside a `∃`.

The result is that `isMFAlgebra_amalgam_of_printedPair` derives Theorem 10 from
this one Prop and a faithful pair of representations, with no other analytic
input.

## This statement is false

`Theorem4PrintedPairStatement` is refuted, twice, and nothing below should be
read as evidence for it.  `Analysis/ShulmanFillNormingPrintedPairRefuted` refutes
it at a one-dimensional `H`, where the printed models have nowhere to go and
`hone` cannot hold; `Analysis/ShulmanFillNormingPrintedPairCharacter` refutes it
at every `H`, because the defects are measured in the sup norm over coordinates,
which forces each fixed finite-dimensional coordinate to be an honest
`*`-homomorphism in the limit and so forces a character on `B` --- and `B(ℂ²)`
is separable, MF and has none.

The legacy tail package is `ShulmanFill.UnitalTailPairPackageStatement`
(`Analysis/ShulmanFillNormingTailPrinted`): the same package with the defects
controlled only past a moving cut, the paper's pointwise lift clause, and `H`
infinite-dimensional.  The route on it is
`Analysis/ShulmanFillNormingTailRoute`.  Everything below stays as the record of
what was refuted and of why the earlier refutation did not reach it.

## Why the scalar-model refutation does not reach this

`Analysis/ShulmanFillNormingTheorem4Refuted` refutes the form of Theorem 4 whose
model is quantified before the representation, and the refutation is the scalar
model: `A n = ℂ`, `ι n z = z • 1` makes `𝒟` commutative while the `lift` clause
is exact, so every separable MF algebra with a faithful representation would be
commutative.  The statement below also fixes its coefficient family before the
representation — but at `B(ℂ^{n+1})`, not at `ℂ`.  Those coefficients are not
commutative, `𝒟` is not commutative, and `commute_of_theorem4ModelFirst` has
nothing to bite on.  What is still quantified after the representation is the
embedding family `ι`, which is where Blackadar--Kirchberg's content sits: the
matricial field is built to fit `π`, and only its *sizes* are prescribed.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-- **Shulman's Theorem 4, Remark 6 and Lemma 9 as one package, at the printed
models.**  For a separable Hilbert space `H`, a separable MF algebra `B`, a
subalgebra map `k : C →⋆ₐ[ℂ] B` and two faithful representations of `B` on `H`
agreeing on `C`, there is one family of contractive embeddings of the printed
coefficients `B(ℂ^{n+1})` into `B(H)` whose units converge strongly to `1`, and
two discrete asymptotic homomorphisms of `B` into the resulting `𝒟` lifting the
two representations and agreeing asymptotically on `C`.

Three clauses of the earlier binders are gone, and none of them by weakening:
the coefficient family is Shulman's own, so `∀ n, HasMFEmbedding (A n)` is a
theorem rather than a hypothesis; there is no existential over types; and the
agreement on `C` — Lemma 9 — is now part of the package, which is what
`ShulmanFill.isMFAlgebra_amalgam_of_doubleLR` actually consumes.

This statement is retained only as the explicitly refuted transcription that
motivated the correction.  Recognition does not cite or consume it. -/
def Theorem4PrintedPairStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {C B : Type} [CStarAlgebra C] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace B] (k : C →⋆ₐ[ℂ] B),
      IsMFAlgebra B →
      ∀ ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H),
        Function.Injective ρ₁ → Function.Injective ρ₂ →
        ρ₁.comp k = ρ₂.comp k →
        ∃ (ι : ∀ n, EllTwoCoefficient n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
          (hnorm : ∀ (n : ℕ) (x : EllTwoCoefficient n), ‖ι n x‖ ≤ ‖x‖)
          (hone : ∀ v : H, Tendsto
            (fun n ↦ ι n (1 : EllTwoCoefficient n) v) atTop (𝓝 v))
          (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
          (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂),
          ∀ c : C, Tendsto
            (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0)

/-! ## Theorem 10 from the package -/

section Consumer

variable [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable [Nontrivial (H →L[ℂ] H)]
variable [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)]
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable [TopologicalSpace.SeparableSpace D]
variable (k : C →⋆ₐ[ℂ] D) [Nonempty (CStarAmalgamRepresentation k k)]

/-- **Shulman's Theorem 10 from the printed package alone.**  Given a faithful
pair of representations of `D` on `H` agreeing on `C`, whose glued limit is
faithful on the double, the package supplies the model, the two lifts and their
agreement; `Analysis/ShulmanFillNormingEllTwoTheorem10` supplies everything
else, `hD` included.  No hypothesis beyond `Theorem4PrintedPairStatement` and
the faithfulness of the pair is used. -/
theorem isMFAlgebra_amalgam_of_printedPair
    (hT4 : Theorem4PrintedPairStatement) (hDmf : IsMFAlgebra D)
    (ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hρ₁ : Function.Injective ρ₁) (hρ₂ : Function.Injective ρ₂)
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective
      (universalCStarAmalgamEval k k (StarStrongAsymptoticLift.limitRep k hρ))) :
    IsMFAlgebra (UniversalCStarAmalgam k k) := by
  obtain ⟨ι, hnorm, hone, φ₁, φ₂, hagree⟩ := hT4 k hDmf ρ₁ ρ₂ hρ₁ hρ₂ hρ
  exact isMFAlgebra_amalgam_of_doubleLR_ellTwo ι hone hnorm k φ₁ φ₂ hagree hρ hΛ

end Consumer

end

end ShulmanFill
end GroupApproximation
