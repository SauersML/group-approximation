import GroupApproximation.Analysis.MaximalCStarParagraphEndpoint
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Kazhdan.KazhdanGenerators
import GroupApproximation.Kazhdan.KazhdanUniverse

/-!
# Strict compression from the group-theoretic hypotheses

The group-theoretic hypothesis is:

> Let `G` contain a property-(T) subgroup `Γ` and an element `t` with
> `t Γ t⁻¹ ⊊ Γ`

and draws from that, and from nothing else, the existence of the Kazhdan
projection `P ∈ Cmax(G)`, the domination `P ≤ u_t P u_t^*`, its strictness,
and the failure of stable finiteness, of a faithful trace, of residual
finite dimensionality and of MF.

`Analysis/MaximalCStarProperCompression` proves all of that, but over a
`StrictKazhdanCompression` datum, which carries a chosen Kazhdan set `Q`, a
chosen tolerance `ε ≤ 1`, and a chosen symmetric generating superset `S`.
Row `MC.07` is precisely the observation that the printed remark asks its
reader for none of these: it asks only for property (T), for containment, and
for strictness.  That is what this file supplies.

The three chosen ingredients are internal, and each comes from an existing
module:

* `Kazhdan/KazhdanFiniteGeneration.exists_symmetric_generating_finset` turns
  property (T) into a finite symmetric generating set containing `1`, by the
  coset-`ℓ²` argument;
* `Kazhdan/KazhdanGenerators.exists_pair_on_generators` turns *that* set into
  a Kazhdan set, by bounding displacement along generator words, and
  `IsKazhdanPair.shrink` normalizes its tolerance to at most `1`;
* `Kazhdan/KazhdanUniverse.HasKazhdanPropertyT.liftUniverse` carries the
  property from representation universe `u` — where the textbook property (T)
  of `hasKazhdanPropertyT_iff_textbook` lives — up to representation universe
  `u + 1`, where the maximal group C-star algebra of a `Type u` group lives.
  This is the free direction of universe transfer and no ascent theorem is
  used.

The printed containment `t Γ t⁻¹ ⊆ Γ` and its strictness are the single
hypothesis `Γ.map (MulAut.conj t).toMonoidHom < Γ`, which is the printed
`t Γ t⁻¹ ⊊ Γ` verbatim: `Subgroup.map` along `MulAut.conj t` is `t Γ t⁻¹`,
and `<` on subgroups is proper containment.

The conclusion is stated as an existential over the projection rather than
over the datum, so that the statement mentions only objects the remark
mentions: `P`, the canonical unitary `u_t = maximalGroupCStarGenerator G t`,
and `Cmax(G)`.
-/

namespace GroupApproximation
namespace MaximalCStarPrintedHypotheses

open MaximalCStarProperCompression

noncomputable section

universe u

-- No section `variable`s: the badged declaration below quantifies over its
-- group arguments inside the proposition, and an in-scope `variable` of the
-- same name would make the unconditionality gate read the elaborated type as
-- carrying a leading input the printed header does not show.

/-- **The printed hypotheses produce a strict Kazhdan compression datum.**

From property (T) for the subgroup `Γ ≤ G` and from `t Γ t⁻¹ ⊊ Γ` alone,
`StrictKazhdanCompression ↥Γ G` is inhabited by a datum whose compressing
element is the given `t`.  The Kazhdan set, its tolerance and the symmetric
generating superset are chosen internally; the printed remark names none of
them.

The returned equation `D.t = t` is what lets the endpoint below phrase the
domination against the canonical unitary of the *printed* element `t`. -/
theorem exists_strictKazhdanCompression {G : Type u} [Group G]
    (Γ : Subgroup G) (t : G)
    (hT : HasKazhdanPropertyT.{u, u} ↥Γ)
    (hlt : Γ.map (MulAut.conj t).toMonoidHom < Γ) :
    ∃ D : StrictKazhdanCompression ↥Γ G, D.t = t := by
  obtain ⟨S, hone, hsymm, hgen⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset ↥Γ hT
  -- the maximal group C-star algebra of `G : Type u` lives in `Type (u + 1)`,
  -- so the pair is needed at representation universe `u + 1`
  have hTup : HasKazhdanPropertyT.{u, u + 1} ↥Γ := hT.liftUniverse
  obtain ⟨δ, hδ⟩ :=
    KazhdanGenerators.exists_pair_on_generators hTup S hsymm hgen
  have hpos : 0 < min δ 1 := lt_min hδ.1 zero_lt_one
  have hcomp : ∀ γ : ↥Γ, ∃ ζ : ↥Γ, t * Γ.subtype γ * t⁻¹ = Γ.subtype ζ := by
    intro γ
    exact ⟨⟨t * (γ : G) * t⁻¹,
      hlt.le (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom γ.2)⟩, rfl⟩
  have hstrict : ∃ a : ↥Γ,
      Γ.subtype a ∉ (Γ.subtype).range.map (MulAut.conj t).toMonoidHom := by
    obtain ⟨x, hxΓ, hxnot⟩ := SetLike.exists_of_lt hlt
    refine ⟨⟨x, hxΓ⟩, ?_⟩
    show x ∉ (Γ.subtype).range.map (MulAut.conj t).toMonoidHom
    rw [Subgroup.range_subtype]
    exact hxnot
  exact ⟨{ iota := Γ.subtype
           t := t
           Q := S
           ε := min δ 1
           kazhdan := IsKazhdanPair.shrink hδ hpos (min_le_left _ _)
           S := S
           QS := Finset.Subset.refl S
           one_mem := hone
           symm := hsymm
           eps_le := min_le_right _ _
           generates := hgen
           compresses := hcomp
           strict := hstrict }, rfl⟩

/-- **The maximal-algebra consequence from its group-theoretic hypotheses.**

The header of the printed remark is exactly the three hypotheses below: `Γ`
is a subgroup of `G`, it has property (T), and `t Γ t⁻¹ ⊊ Γ`.  No Kazhdan
set, tolerance or generating set is asked of the reader.

The conclusions follow the printed sentences:

* the Kazhdan projection `P` exists in `Cmax(G)` — self-adjoint and
  idempotent there;
* conjugation by `u_t` dominates it, on both sides;
* the domination is strict;
* hence `Cmax(G)` is not Dedekind finite, not stably finite, carries no
  faithful tracial state, and in particular is neither residually
  finite-dimensional nor MF, in both the bare-embedding and the separable
  senses;
* in contrast, the reduced algebra of the same group carries a faithful
  canonical trace and admits no proper compression at all, so its failure of
  MF is not a failure of finiteness.

This is `MaximalCStarParagraphEndpoint.manuscriptMaximalCStarStrictCompressionRemark`
with the datum discharged: that declaration quantifies over
`StrictKazhdanCompression`, this one over the printed hypotheses that produce
it. -/
def MaximalCStarRemarkFromPrintedHypotheses : Prop :=
  ∀ (G : Type u) [Group G] (Γ : Subgroup G) (t : G),
    HasKazhdanPropertyT.{u, u} ↥Γ →
    Γ.map (MulAut.conj t).toMonoidHom < Γ →
    (∃ P : MaximalGroupCStar G,
        IsSelfAdjoint P ∧
        P * P = P ∧
        (maximalGroupCStarGenerator G t * P *
            star (maximalGroupCStarGenerator G t)) * P = P ∧
        P * (maximalGroupCStarGenerator G t * P *
            star (maximalGroupCStarGenerator G t)) = P ∧
        maximalGroupCStarGenerator G t * P *
            star (maximalGroupCStarGenerator G t) ≠ P) ∧
      ¬ IsDedekindFiniteMonoid (MaximalGroupCStar G) ∧
      ¬ IsStablyFiniteRing (MaximalGroupCStar G) ∧
      ¬ Nonempty (FaithfulTracialState (MaximalGroupCStar G)) ∧
      ¬ IsResiduallyFiniteDimensional (MaximalGroupCStar G) ∧
      ¬ HasMFEmbedding (MaximalGroupCStar G) ∧
      ¬ IsMFAlgebra (MaximalGroupCStar G) ∧
      Nonempty (FaithfulTracialState
        (ReducedGroupCStarTrace.ReducedGroupCStar G)) ∧
      IsEmpty (ProperProjectionCompression
        (ReducedGroupCStarTrace.ReducedGroupCStar G))

/-- **The printed strict-compression remark, as a closed proposition.**

`#audit_closed_axioms` refuses any advertised endpoint whose elaborated type
is itself a pi type, because a caller-supplied binder is indistinguishable
from construction data at that level.  The hypotheses here are not supplied
by a caller -- they are universally quantified inside the statement -- so the
remark is closed, and naming it is what lets the guard see that.  This is the
same idiom the manuscript endpoints use (`NormalKazhdanRadical`,
`OneSidedCompressionCriterion`).  The proposition is unchanged. -/
theorem manuscriptMaximalCStarRemarkFromPrintedHypotheses :
    MaximalCStarRemarkFromPrintedHypotheses.{u} := by
  intro G _ Γ t hT hlt
  obtain ⟨D, hDt⟩ := exists_strictKazhdanCompression Γ t hT hlt
  have hshift : D.shift = maximalGroupCStarGenerator G t := by
    show maximalGroupCStarGenerator G D.t = maximalGroupCStarGenerator G t
    rw [hDt]
  refine ⟨⟨D.proj, D.isSelfAdjoint_proj, D.proj_mul_proj, ?_, ?_, ?_⟩,
    D.maximalCStar_not_isDedekindFiniteMonoid,
    D.maximalCStar_not_isStablyFiniteRing,
    D.maximalCStar_no_faithfulTracialState,
    D.toProperProjectionCompression.not_isResiduallyFiniteDimensional,
    D.toProperProjectionCompression.not_hasMFEmbedding,
    D.toProperProjectionCompression.not_isMFAlgebra,
    ⟨ReducedGroupCStarTrace.canonicalFaithfulTracialState G⟩,
    ReducedGroupCStarTrace.reduced_no_properProjectionCompression G⟩
  · rw [← hshift]
    exact D.conjugate_mul_proj
  · rw [← hshift]
    exact D.proj_mul_conjugate
  · rw [← hshift]
    exact D.conjugate_ne_proj

end

end MaximalCStarPrintedHypotheses
end GroupApproximation
