import GroupApproximation.Analysis.ShulmanFillNormingFactorMapComp

/-!
# Faithfulness of the factor map does not depend on the faithful target

`ShulmanFill.shulmanTheorem16_of_typeZeroWitness` asks its witness hypothesis
for injectivity of `factorAmalgamToSymmetricTarget … g` for **every** faithful
`Type`-valued `g` out of the symmetric double, whereas
`ShulmanSymmetricDouble.CompatibleTargetPairStatement` produces exactly one
target.  This module closes that gap: one faithful target is as good as all of
them.

Only `g` has to be faithful.  Nothing is asked of `g₀` beyond the injectivity of
its own factor map — which matters, because `CompatibleTargetPairStatement`
supplies `g₀` as the evaluation at a compatible pair and claims no faithfulness
for it at all.

The argument cannot factor through the amalgam's embedding into the double —
that map is untypable, as the header of
`Analysis/ShulmanFillNormingAmalgamWitness` shows — so it goes through the range
of `g` instead.  `StarAlgEquiv.ofInjective` corestricts `g` to a
`*`-isomorphism onto `g.range`, so `g₀ = (g₀ ∘ g⁻¹) ∘ g`, and
`Analysis/ShulmanFillNormingFactorMapComp.factorAmalgamToSymmetricTarget_comp`
moves the factor map across that composition and across
`g = g.range.subtype ∘ g.rangeRestrict`.  The double is never named outside the
type of `g`, so no universe descent occurs.

## The one instance that has to be built

`factorAmalgamToSymmetricTarget` needs its carrier to be a nontrivial C-star
algebra, and `↥g.range` is one only because `g` is isometric:
`StarSubalgebra.cstarAlgebra` takes `IsClosed (s : Set A)` as an *instance*
argument, and nothing supplies it for a range.  `isClosed_starAlgHom_range`
builds it — an injective `*`-homomorphism of C-star algebras is isometric
(`NonUnitalStarAlgHom.isometry`), an isometry out of a complete space is a
closed embedding (`Isometry.isClosedEmbedding`), and its `isClosed_range` field
is the set.  `nontrivial_starAlgHom_range` is the matching nontriviality, which
has no subalgebra instance either and is read off a pair of distinct points of
the source.
-/

namespace GroupApproximation
namespace MFAlgebraAmalgamCriterion

open scoped CStarAlgebra

noncomputable section

universe u v

/-! ## The universal amalgam is nontrivial

`ShulmanFill.nontrivial_universalCStarAmalgam` of
`Analysis/ShulmanFillNormingCoronaRoute` says this already, but that module sits
at the top of the `ShulmanFill` route and importing it here would make a
low-level piece of amalgam machinery depend on it.  The argument is four lines,
so it is repeated rather than imported. -/

theorem nontrivial_universalCStarAmalgam_of_nonempty
    {C A B : Type} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)] :
    Nontrivial (UniversalCStarAmalgam iA iB) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro hone
  have R : CStarAmalgamRepresentation iA iB := Classical.arbitrary _
  have h := congrArg (universalCStarAmalgamEval iA iB R) hone
  rw [map_one, map_zero] at h
  exact one_ne_zero h

/-! ## The range of an injective `*`-homomorphism

The source is left in its own universe: the only source this is ever applied to
is `UniversalCStarAmalgam gamma gamma`, which lies one universe above `C`, `A`,
`B` — it is a subalgebra of a product indexed by a `Type`-valued structure — so a
`{U : Type}` here would not typecheck at the one call site that matters. -/

section Range

variable {U : Type u} {E : Type v} [CStarAlgebra U] [CStarAlgebra E]

/-- **The range of an injective `*`-homomorphism is closed.**  It is isometric
onto its image, and an isometry out of a complete space is a closed
embedding. -/
theorem isClosed_starAlgHom_range (g : U →⋆ₐ[ℂ] E) (hg : Function.Injective g) :
    IsClosed ((g.range : StarSubalgebra ℂ E) : Set E) := by
  have hiso : Isometry (g : U → E) :=
    NonUnitalStarAlgHom.isometry g.toNonUnitalStarAlgHom hg
  have hset : ((g.range : StarSubalgebra ℂ E) : Set E) = Set.range (g : U → E) := by
    ext y
    exact ⟨fun hy ↦ ⟨hy.choose, hy.choose_spec⟩,
      fun hy ↦ ⟨hy.choose, hy.choose_spec⟩⟩
  rw [hset]
  exact hiso.isClosedEmbedding.isClosed_range

/-- **The range of an injective `*`-homomorphism out of a nontrivial algebra is
nontrivial.**  There is no subalgebra instance for this, and
`factorAmalgamToSymmetricTarget` asks for it at every carrier. -/
theorem nontrivial_starAlgHom_range [Nontrivial U] (g : U →⋆ₐ[ℂ] E)
    (hg : Function.Injective g) :
    Nontrivial (g.range : StarSubalgebra ℂ E) := by
  -- `a`, `b` rather than `u`, `v`: those name the universes of this section.
  obtain ⟨a, b, hab⟩ := exists_pair_ne U
  exact ⟨⟨g.rangeRestrict a, g.rangeRestrict b,
    fun h ↦ hab (hg (Subtype.ext_iff.mp h))⟩⟩

end Range

/-! ## The transfer -/

section Transfer

variable {C A B D E E' : Type}
  [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
  [CStarAlgebra D] [Nontrivial D] [CStarAlgebra E] [Nontrivial E]
  [CStarAlgebra E'] [Nontrivial E']

/-- **One target is as good as all the faithful ones.**  If the factor map into
*some* `Type`-valued image of the symmetric double is injective, then so is the
factor map into every **faithful** image.

Note what is and is not asked of `g₀`: only that its factor map separates, not
that `g₀` itself does.  That is what makes this usable, because
`ShulmanSymmetricDouble.CompatibleTargetPairStatement` supplies exactly such a
`g₀` — the evaluation at a compatible pair, with no faithfulness claimed for it —
and it is what turns that statement into the `hwit` hypothesis of
`ShulmanFill.shulmanTheorem16_of_typeZeroWitness`, which quantifies over every
faithful target.

Faithfulness of `g` is what lets `g₀` be rewritten through it: `g` corestricts
to a `*`-isomorphism onto its range, so `g₀ = (g₀ ∘ g⁻¹) ∘ g` with `g⁻¹` the
inverse of that isomorphism, and
`factorAmalgamToSymmetricTarget_comp` moves the factor map across both
compositions. -/
theorem injective_factorAmalgamToSymmetricTarget_of_injective_target
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (gamma : C →⋆ₐ[ℂ] D) (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
    (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma)
    (g₀ : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E')
    (hfac : Function.Injective
      (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB g₀))
    (g : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E)
    (hg : Function.Injective g) :
    Function.Injective
      (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB g) := by
  haveI : Nontrivial (UniversalCStarAmalgam gamma gamma) :=
    nontrivial_universalCStarAmalgam_of_nonempty gamma gamma
  haveI : IsClosed ((g.range : StarSubalgebra ℂ E) : Set E) :=
    isClosed_starAlgHom_range g hg
  haveI : Nontrivial (g.range : StarSubalgebra ℂ E) :=
    nontrivial_starAlgHom_range g hg
  -- From here `↥g.range` carries two routes to its ring, algebra and star
  -- structure: the `StarSubalgebra` one, which `StarAlgEquiv.ofInjective` is
  -- stated at, and the one `StarSubalgebra.cstarAlgebra` supplies, which is what
  -- `factorAmalgamToSymmetricTarget` reads off its `[CStarAlgebra E]` argument.
  -- The two are definitionally equal but not syntactically so, and `rw`
  -- type-checks at `instances` transparency — exactly where they part.  So the
  -- inverse is introduced through an ascription at the second route, and every
  -- transport below is `congrArg` at the *applied* level, where the head of the
  -- pattern is `g₀` or `g` and no instance is in question.
  have hinv_apply : ∀ x : UniversalCStarAmalgam gamma gamma,
      ((StarAlgEquiv.ofInjective g hg).symm.toStarAlgHom :
        (g.range : StarSubalgebra ℂ E) →⋆ₐ[ℂ]
          UniversalCStarAmalgam gamma gamma) (g.rangeRestrict x) = x :=
    fun x ↦ (StarAlgEquiv.ofInjective g hg).symm_apply_apply x
  have hpsi : (g₀.comp
        ((StarAlgEquiv.ofInjective g hg).symm.toStarAlgHom :
          (g.range : StarSubalgebra ℂ E) →⋆ₐ[ℂ]
            UniversalCStarAmalgam gamma gamma)).comp g.rangeRestrict = g₀ := by
    refine StarAlgHom.ext fun x ↦ ?_
    show g₀ (((StarAlgEquiv.ofInjective g hg).symm.toStarAlgHom :
        (g.range : StarSubalgebra ℂ E) →⋆ₐ[ℂ]
          UniversalCStarAmalgam gamma gamma) (g.rangeRestrict x)) = g₀ x
    rw [hinv_apply]
  have hcong := congrArg
    (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB) hpsi
  have h1 : Function.Injective
      (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB
        g.rangeRestrict) := by
    refine injective_factorAmalgamToSymmetricTarget_of_comp iA iB gamma alpha
      beta hA hB g.rangeRestrict
      (g₀.comp ((StarAlgEquiv.ofInjective g hg).symm.toStarAlgHom :
        (g.range : StarSubalgebra ℂ E) →⋆ₐ[ℂ]
          UniversalCStarAmalgam gamma gamma)) ?_
    intro x y hxy
    apply hfac
    rw [← DFunLike.congr_fun hcong x, ← DFunLike.congr_fun hcong y]
    exact hxy
  have hsub : (g.range : StarSubalgebra ℂ E).subtype.comp g.rangeRestrict = g :=
    StarAlgHom.ext fun _ ↦ rfl
  have hcong2 := congrArg
    (factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB) hsub
  have h2 := injective_factorAmalgamToSymmetricTarget_comp iA iB gamma alpha
    beta hA hB g.rangeRestrict (g.range : StarSubalgebra ℂ E).subtype
    (fun _ _ h ↦ Subtype.ext h) h1
  intro x y hxy
  apply h2
  exact (DFunLike.congr_fun hcong2 x).trans
    (hxy.trans (DFunLike.congr_fun hcong2 y).symm)

end Transfer

end

end MFAlgebraAmalgamCriterion
end GroupApproximation
