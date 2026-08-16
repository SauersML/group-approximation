import GroupApproximation.Sofic.AscendingHNNCosetActionSofic
import GroupApproximation.Sofic.AscendingHNNWreathSofic
import GroupApproximation.Sofic.SoficActionChabauty

/-!
# The coset action is sofic as soon as the base copy is separable

Fournier-Facio's question asks whether the coset action `G ↷ G/Γ` of an
ascending HNN extension is sofic when the base is residually finite and the
self-embedding has infinite index.  Two flanking cases are closed:
finite-index image (`isSoficAction_vertical_cosets`), and arbitrary image over
a universally action-sofic base (`isSoficAction_vertical_cosets_of_uas`), which
covers LERF and LERA.

Both known routes over-assume.  UAS asks that *every* action of the base be
sofic; the LERF route asks that *every* finitely generated subgroup of the base
be separable.  The action in question has one point stabiliser, so only that
one subgroup can matter.  `Cosets` is by definition the quotient of `Vertical`
by `(iotaVertical α hα).range`, so the transitive criterion
`isSoficAction_quotient_of_separable` applies to it directly:

**separability of the single subgroup `Γ ≤ G` is enough.**

That is the sharp hypothesis, and it moves the open question off soficity and
onto a classical subgroup-separability statement about one explicit subgroup.

## What separability of `Γ` in `G` unwinds to

The reduction is worth recording, because it explains both why LERF succeeds
and why residual finiteness is the wrong hypothesis to hope for.

Write `N = ⋃ₙ t⁻ⁿΓtⁿ` for the kernel of `G → ℤ`, so `Γ ≤ N` and `N` is the
increasing union of the levels `Γ₋ₙ = t⁻ⁿΓtⁿ`.  Let `L ≤ G` have finite index
with `Γ ≤ L`, and put `M = L ∩ N`, of finite index `m` in `N`.  Conjugating the
`n`-th level back to the base, `Mₙ := tⁿ(M ∩ Γ₋ₙ)t⁻ⁿ` is a subgroup of `Γ` of
index at most `m`, and the levels of `M` fit together exactly as

  `Mₙ = α⁻¹(Mₙ₊₁)`,  equivalently  `α(Mₙ) ≤ Mₙ₊₁`,  with  `M₀ = Γ`.

Now take `γ' = t⁻¹γt ∈ Γ₋₁ \ Γ`, which is to say `γ ∈ Γ \ α(Γ)`.  Then
`γ' ∈ M` iff `γ ∈ M₁`, so excluding `γ'` from `L` means exactly:

  a finite-index `M₁ ≤ Γ` with `α(Γ) ≤ M₁` and `γ ∉ M₁`

-- separability of `α(Γ)` in `Γ`.  Excluding a general `γ' ∈ Γ₋ₖ` needs the
whole tower: finite-index `Mₖ` of uniformly bounded index with `α(Mₖ₋₁) ≤ Mₖ`
and `α^{k-1}(γ) ∉ Mₖ`.  One cannot shortcut by taking `Mₖ = Γ` for large `k`,
since then `M` swallows the level containing `γ'`.

So the hypothesis is a *tower* of separability statements for the subgroups
`α^k(Γ)` and their finite-index refinements -- each of infinite index in `Γ`
once the embedding has infinite index.  Over a LERF base the tower is free:
every `Mₖ` may be taken finitely generated and separability is automatic.
Residual finiteness says nothing about it: it separates elements from `1`, and
the tower asks to separate elements from infinite-index subgroups.  Nothing
here suggests residual finiteness suffices, and this file does not claim it
does; it isolates precisely the statement that would have to be proved.
-/

namespace GroupApproximation
namespace MarkedCompression

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

include hα in
/-- **The sharp separability criterion.**  If the base copy of `Γ` is a
separable subgroup of the ascending HNN extension -- every element outside it
is excluded by some finite-index subgroup containing it -- then the coset
action is sofic.

This is strictly weaker than the two hypotheses already in the tree.  Universal
action soficity constrains every action of the base at once, and the LERF route
constrains every finitely generated subgroup of the base; this constrains one
subgroup of `G`, the stabiliser of the point whose orbit is being modelled. -/
theorem isSoficAction_vertical_cosets_of_separable_base
    (hsep : ∀ g : Vertical α hα, g ∉ (iotaVertical α hα).range →
      ∃ K : Subgroup (Vertical α hα),
        (iotaVertical α hα).range ≤ K ∧ K.FiniteIndex ∧ g ∉ K) :
    IsSoficAction (Vertical α hα) (Cosets α hα) :=
  isSoficAction_quotient_of_separable (iotaVertical α hα).range hsep

end MarkedCompression

namespace AscendingHNNWreath

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

include hα in
/-- The wreath product over the coset space is then sofic for any sofic lamp,
given soficity of the base.

The separability hypothesis is on a subgroup of `G`, not on the base as an
abstract group, so soficity of `Γ` is still assumed separately.  That is the
one respect in which this is weaker than the LERF corollary beside it: there,
separability of every finitely generated subgroup already forced the base to be
residually finite, hence sofic, and no soficity hypothesis was needed. -/
theorem isSofic_wreath_cosets_of_separable_base {K : Type} [Group K]
    (hΓ : IsSofic Γ) (hK : IsSofic K)
    (hsep : ∀ g : MarkedCompression.Vertical α hα,
        g ∉ (MarkedCompression.iotaVertical α hα).range →
      ∃ L : Subgroup (MarkedCompression.Vertical α hα),
        (MarkedCompression.iotaVertical α hα).range ≤ L ∧ L.FiniteIndex ∧ g ∉ L) :
    IsSofic (Wreath K (MarkedCompression.Vertical α hα)
      (MarkedCompression.Cosets α hα)) :=
  GeneralizedWreath.isSofic_wreath hK (isSofic_vertical α hα hΓ)
    (MarkedCompression.isSoficAction_vertical_cosets_of_separable_base α hα hsep)

end AscendingHNNWreath

end GroupApproximation
