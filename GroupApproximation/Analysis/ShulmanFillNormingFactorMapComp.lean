import GroupApproximation.Analysis.MFAlgebraAmalgamFactorMap

/-!
# The factor map is functorial in its target

`MFAlgebraAmalgamCriterion.factorAmalgamToSymmetricTarget iA iB gamma alpha beta
hA hB e` takes a `*`-homomorphism `e` out of the symmetric double and produces
one out of the amalgam `A *_C B`.  The headers of
`Analysis/ShulmanFillNormingAmalgamWitness` and
`Analysis/ShulmanFillSymmetricDoubleEmbedTheorem13` both appeal to a lemma
`factorAmalgamToSymmetricTarget_eq_comp`, saying the factor map "is `g ∘ e`" —
but no such lemma exists in the repository, and the map it names cannot be
written: the intermediate embedding `A *_C B →⋆ₐ[ℂ] D *_C D` is exactly the one
the AmalgamWitness header shows is untypable, because
`UniversalCStarAmalgam gamma gamma` lives one universe above `C`, `A` and `B`.

What is true, and provable without naming that map, is functoriality in the
*target*: post-composing `e` post-composes the factor map.

    `factor … (h.comp e) = h.comp (factor … e)`

Both sides are `*`-homomorphisms out of the amalgam taking the same values on
the two factor images — `universalCStarAmalgamEval_left` and `_right` are `rfl`,
so the two obligations are `rfl` — and the uniqueness half of
`universalCStarAmalgam_existsUnique_lift` identifies them.  No universe descent
occurs anywhere, because the double is never mentioned outside `e`'s type.

That is enough for the two directions of faithfulness transfer that need no
further input, `injective_factorAmalgamToSymmetricTarget_comp` and
`injective_factorAmalgamToSymmetricTarget_of_comp` below.  What it is *not* yet
enough for is the `hwit` hypothesis of
`ShulmanFill.shulmanTheorem16_of_typeZeroWitness`, which quantifies over every
faithful target: passing between two unrelated faithful `g`, `g₀` needs the
`*`-isomorphism `g.range ≃⋆ₐ g₀.range`, hence `StarAlgEquiv.ofInjective`
together with closedness of the range of an injective `*`-homomorphism, and
that step is not in this module.
-/

namespace GroupApproximation
namespace MFAlgebraAmalgamCriterion

noncomputable section

variable {C A B D E E' : Type}
  [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
  [CStarAlgebra D] [Nontrivial D] [CStarAlgebra E] [Nontrivial E]
  [CStarAlgebra E'] [Nontrivial E']

/-- **The factor map is functorial in its target.**  Post-composing the
homomorphism out of the symmetric double post-composes the factor map.  This is
the usable form of the `factorAmalgamToSymmetricTarget_eq_comp` that the headers
of `Analysis/ShulmanFillNormingAmalgamWitness` and
`Analysis/ShulmanFillSymmetricDoubleEmbedTheorem13` appeal to: it says what that
lemma wanted to say, without naming the untypable embedding of the amalgam into
the double. -/
theorem factorAmalgamToSymmetricTarget_comp
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (gamma : C →⋆ₐ[ℂ] D) (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
    (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma)
    (e : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E) (h : E →⋆ₐ[ℂ] E') :
    factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB (h.comp e)
      = h.comp
        (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB e) := by
  obtain ⟨f, _hf, huniq⟩ :=
    universalCStarAmalgam_existsUnique_lift iA iB
      ((h.comp e).comp ((universalCStarAmalgamLeft gamma gamma).comp alpha))
      ((h.comp e).comp ((universalCStarAmalgamRight gamma gamma).comp beta))
      (factorToSymmetricTargetRepresentation iA iB gamma alpha beta hA hB
        (h.comp e)).compatible
  have hleft := huniq
    (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB (h.comp e))
    ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hright := huniq
    (h.comp (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB e))
    ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact hleft.trans hright.symm

/-- **Faithfulness passes forward along a faithful post-composition.** -/
theorem injective_factorAmalgamToSymmetricTarget_comp
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (gamma : C →⋆ₐ[ℂ] D) (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
    (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma)
    (e : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E) (h : E →⋆ₐ[ℂ] E')
    (hh : Function.Injective h)
    (he : Function.Injective
      (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB e)) :
    Function.Injective
      (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB
        (h.comp e)) := by
  intro x y hxy
  apply he
  apply hh
  have hx := DFunLike.congr_fun
    (factorAmalgamToSymmetricTarget_comp iA iB gamma alpha beta hA hB e h) x
  have hy := DFunLike.congr_fun
    (factorAmalgamToSymmetricTarget_comp iA iB gamma alpha beta hA hB e h) y
  rw [hx, hy] at hxy
  exact hxy

/-- **Faithfulness passes backward along any post-composition.**  If the factor
map of the composite separates, so does the factor map of the inner
homomorphism, whatever `h` is. -/
theorem injective_factorAmalgamToSymmetricTarget_of_comp
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (gamma : C →⋆ₐ[ℂ] D) (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
    (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma)
    (e : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E) (h : E →⋆ₐ[ℂ] E')
    (hcomp : Function.Injective
      (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB
        (h.comp e))) :
    Function.Injective
      (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB e) := by
  intro x y hxy
  apply hcomp
  have hx := DFunLike.congr_fun
    (factorAmalgamToSymmetricTarget_comp iA iB gamma alpha beta hA hB e h) x
  have hy := DFunLike.congr_fun
    (factorAmalgamToSymmetricTarget_comp iA iB gamma alpha beta hA hB e h) y
  rw [hx, hy]
  exact congrArg h hxy

end

end MFAlgebraAmalgamCriterion
end GroupApproximation
