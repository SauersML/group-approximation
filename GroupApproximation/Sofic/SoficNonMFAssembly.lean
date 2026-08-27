import GroupApproximation.Sofic.AscendingHNNWreathSofic
import GroupApproximation.Sofic.AscendingHNNWreathWitness
import GroupApproximation.Sofic.SoficActionOrbits

/-!
# Theorems 34.5 and 34.6: sofic **and** non-MF, in one statement

Sections 34.5 and 34.6 are the dossier's headline, and both are assemblies: the
non-MF half and the sofic half are proved by completely disjoint arguments and
are simply conjoined.  Everything they consume is already formalised, so this
file only puts the pieces together.

* Non-MF is Theorem 34.4, `MarkedCompression.not_isCDEOperatorMF_wreath`, and it
  uses neither hypothesis added in 34.5 or 34.6: a property-`(T)` group with a
  *proper* injective self-embedding suffices.
* Soficity is Theorem 29.6 (`GeneralizedWreath.isSofic_wreath`) applied to a
  sofic lamp group, the sofic ascending-HNN extension of Section 11
  (`isSofic_vertical`), and a sofic coset action.  The coset action is where
  34.5 and 34.6 differ: 34.5 gets it from finite index (Theorem 13.5), 34.6 from
  universal action-soficity (Theorem 31.2), with no index hypothesis at all.

`isSofic_and_not_isCDEOperatorMF_of_finiteIndex` is Theorem 34.5,
`isSofic_and_not_isCDEOperatorMF_of_uas` is Theorem 34.6, and
`isSofic_and_not_isCDEOperatorMF_of_isLERA` is Corollary 34.7.

## One hypothesis the dossier derives and this file does not

Theorems 34.6 and 34.7 read "UAS implies that `Γ` is sofic" and "LERA implies
sofic" as steps, and do not carry soficity of the base as a hypothesis.  Here it
*is* carried, as `hΓ : IsSofic Γ`.  The reason is structural rather than
mathematical: `IsSofic` is stated with models in `Type 0` while
`SoficActionModel` keeps its model set in the universe of the acted-on type, so
turning the regular action's models into group models is a universe question
this file does not settle.  The implication is not in the repository, so it is
not assumed silently -- the hypothesis is written out instead.  Discharging it
would remove `hΓ` from the last two theorems and nothing else.
-/

namespace GroupApproximation

namespace MarkedCompression

open MappingTelescope SemidirectProduct

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)
variable {K : Type} [Group K] [DecidableEq (Cosets α hα)]

include hα in
/-- **Theorem 34.5.**  A sofic property-`(T)` base with a *finite-index* proper
injective self-embedding, and any sofic lamp group with an involution, gives a
permutational wreath product that is sofic and not MF.

The two halves share no input beyond the group: non-MF-ness needs only property
`(T)` and properness of the embedding, while soficity needs only soficity of the
base and of the lamps together with the finite-index hypothesis. -/
theorem isSofic_and_not_isCDEOperatorMF_of_finiteIndex
    [α.range.FiniteIndex] [Countable (WreathV (K := K) α hα)]
    (hΓ : IsSofic Γ) (hK : IsSofic K)
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
    {k₀ : K} (hk₀ : k₀ ≠ 1) (hk2 : k₀ * k₀ = 1)
    {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    IsSofic (WreathV (K := K) α hα) ∧
      ¬ IsCDEOperatorMF (WreathV (K := K) α hα) :=
  ⟨AscendingHNNWreath.isSofic_wreath_cosets α hα hΓ hK,
    not_isCDEOperatorMF_wreath α hα hT hk₀ hk2 ha₀⟩

omit [DecidableEq (Cosets α hα)] in
include hα in
/-- The soficity half of Theorem 34.6: over a universally action-sofic base the
wreath product is sofic for an **arbitrary** injective self-embedding.  No
finite-index hypothesis appears; Theorem 31.2 supplies the coset action. -/
theorem isSofic_wreath_cosets_of_uas
    (hUAS : UniversallyActionSofic Γ) (hΓ : IsSofic Γ) (hK : IsSofic K) :
    IsSofic (WreathV (K := K) α hα) :=
  GeneralizedWreath.isSofic_wreath hK
    (AscendingHNNWreath.isSofic_vertical α hα hΓ)
    (isSoficAction_vertical_cosets_of_uas α hα hUAS)

include hα in
/-- **Theorem 34.6.**  Over a universally action-sofic property-`(T)` base, any
proper injective self-embedding gives a wreath product that is sofic and not MF
-- the finite-index restriction of 34.5 is gone. -/
theorem isSofic_and_not_isCDEOperatorMF_of_uas
    [Countable (WreathV (K := K) α hα)]
    (hUAS : UniversallyActionSofic Γ) (hΓ : IsSofic Γ) (hK : IsSofic K)
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
    {k₀ : K} (hk₀ : k₀ ≠ 1) (hk2 : k₀ * k₀ = 1)
    {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    IsSofic (WreathV (K := K) α hα) ∧
      ¬ IsCDEOperatorMF (WreathV (K := K) α hα) :=
  ⟨isSofic_wreath_cosets_of_uas α hα hUAS hΓ hK,
    not_isCDEOperatorMF_wreath α hα hT hk₀ hk2 ha₀⟩

include hα in
/-- **Corollary 34.7.**  The same conclusion for a LERA base, which is the
cleanest abstract route to the headline: property `(T)`, LERA, and
non-co-Hopfian -- the last being exactly the existence of the proper injective
`α`.  The stronger LERF hypothesis factors through
`universallyActionSofic_of_fg_separable` in the same way. -/
theorem isSofic_and_not_isCDEOperatorMF_of_isLERA
    [Countable (WreathV (K := K) α hα)]
    (hlera : IsLERA Γ) (hΓ : IsSofic Γ) (hK : IsSofic K)
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
    {k₀ : K} (hk₀ : k₀ ≠ 1) (hk2 : k₀ * k₀ = 1)
    {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    IsSofic (WreathV (K := K) α hα) ∧
      ¬ IsCDEOperatorMF (WreathV (K := K) α hα) :=
  isSofic_and_not_isCDEOperatorMF_of_uas α hα
    (universallyActionSofic_of_isLERA hlera) hΓ hK hT hk₀ hk2 ha₀

end MarkedCompression

end GroupApproximation
