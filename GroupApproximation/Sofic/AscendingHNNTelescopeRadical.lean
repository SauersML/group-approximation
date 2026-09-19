import GroupApproximation.Sofic.AscendingHNNSplitExtension
import GroupApproximation.Algebra.CountableInstances

/-!
# The lamp differences of the first collapse stage lie in the MF radical

**Sections 37 and 47** of the ascending-HNN dossier, the inclusion half, for
the involutive witness class where the analytic input is unconditional.

The collapse commutator of the witness lamp is not an abstract element: it is a
*lamp difference*, the configuration carrying the value `k` at one site and
`k⁻¹` at another,

    ⁅ι γ, witnessLamp k⁆ = lampDiff (ι γ • tΓ) (tΓ) k.

That single computation is what turns the compression-collapse theorem into a
statement about the site set.  Conjugating by the acting group transports a
difference to any translate of the pair (`conj_lampDiff`), and the collapse
defect is normal, so the differences available at the first stage are exactly
those along a base move applied at an arbitrary site:

    lampDiff ((g · ι γ) • tΓ) (g • tΓ) k  ∈  involutiveCollapseDefect.

`Sofic/InvolutionCollapseEndpoint` then puts all of them in the literal MF
radical with no analytic hypothesis left, and `stageRadical_ne_bot` says the
subgroup they generate is not trivial as soon as the self-embedding is proper:
the group really does have an invisible part.

What is *not* here is the passage from one stage to the telescope.  A base move
shifts a coset by the level `-1` copy `t⁻¹ ι(Γ) t` only; reaching the whole
telescope `⋃ₙ t⁻ⁿ ι(Γ) tⁿ` means iterating the collapse on the quotient, and
the union step of that iteration is `Algebra/WreathTelescopeUnion`.  The two
ends are formalized; the induction that joins them is not.
-/

namespace GroupApproximation
namespace MarkedCompression

open SemidirectProduct MappingTelescope InvolutionCollapseEndpoint
open scoped commutatorElement

variable {Γ₀ : Type} [Group Γ₀] (β : Γ₀ →* Γ₀) (hβ : Function.Injective β)
variable {K₀ : Type} [Group K₀] [DecidableEq (Cosets β hβ)]

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-- The lamp difference: the value `k` at one site against the same value at
another.  Every collapse commutator of the witness lamp has this shape. -/
def lampDiff (x y : Cosets β hβ) (k : K₀) : WreathV (K := K₀) β hβ :=
  inl (Lamp.single x k * (Lamp.single y k)⁻¹)

/-- A difference of a site with itself is trivial. -/
theorem lampDiff_self (x : Cosets β hβ) (k : K₀) :
    lampDiff β hβ x x k = 1 := by
  rw [lampDiff, mul_inv_cancel, map_one]

/-- **The collapse commutator is a lamp difference.**  This is the whole bridge
between the compression-collapse theorem and the site set. -/
theorem commutator_eq_lampDiff (γ : Γ₀) (k : K₀) :
    ⁅(inr (iotaVertical β hβ γ) : WreathV (K := K₀) β hβ),
        witnessLamp β hβ k⁆
      = lampDiff β hβ (iotaVertical β hβ γ • tSite β hβ) (tSite β hβ) k := by
  rw [commutatorElement_def, conj_witnessLamp, witnessLamp, ← map_inv,
    ← map_mul]
  rfl

/-- **Transport.**  Conjugating a lamp difference by the acting group translates
both of its sites. -/
theorem conj_lampDiff (g : Vertical β hβ) (x y : Cosets β hβ) (k : K₀) :
    (inr g : WreathV (K := K₀) β hβ) * lampDiff β hβ x y k * (inr g)⁻¹
      = lampDiff β hβ (g • x) (g • y) k := by
  rw [lampDiff, ← map_inv, ← SemidirectProduct.inl_aut]
  refine congrArg inl ?_
  have hx : (lampActionHom (K := K₀) g) (Lamp.single x k)
      = Lamp.single (g • x) k := lampAut_single g x k
  have hy : (lampActionHom (K := K₀) g) (Lamp.single y k)
      = Lamp.single (g • y) k := lampAut_single g y k
  rw [map_mul, map_inv, hx, hy]

include hβ in
/-- The base-move difference at the witness site lies in the involutive
collapse defect: it *is* a collapse commutator. -/
theorem lampDiff_base_mem_defect {k : K₀} (hk2 : k * k = 1) (γ : Γ₀) :
    lampDiff β hβ (iotaVertical β hβ γ • tSite β hβ) (tSite β hβ) k
      ∈ involutiveCollapseDefect (baseSub β hβ) (wreathT β hβ) := by
  rw [involutiveCollapseDefect, ← commutator_eq_lampDiff]
  refine Subgroup.subset_normalClosure ⟨witnessLamp β hβ k,
    isInvolutiveCompressionWitness_witnessLamp β hβ hk2,
    inr (iotaVertical β hβ γ), (mem_baseSub_iff β hβ).mpr ⟨γ, rfl⟩, rfl⟩

include hβ in
/-- **Every base move, at every site.**  Normality of the defect turns the one
computation at the witness site into a difference along a base move applied
anywhere in the coset space. -/
theorem lampDiff_mem_defect {k : K₀} (hk2 : k * k = 1) (g : Vertical β hβ)
    (γ : Γ₀) :
    lampDiff β hβ ((g * iotaVertical β hβ γ) • tSite β hβ) (g • tSite β hβ) k
      ∈ involutiveCollapseDefect (baseSub β hβ) (wreathT β hβ) := by
  have hconj := (involutiveCollapseDefect_normal (baseSub β hβ)
      (wreathT β hβ)).conj_mem _ (lampDiff_base_mem_defect β hβ hk2 γ) (inr g)
  rwa [conj_lampDiff, ← mul_smul] at hconj

/-- The base-move differences of a fixed lamp value. -/
def baseMoveSet (k : K₀) : Set (WreathV (K := K₀) β hβ) :=
  {w | ∃ (g : Vertical β hβ) (γ : Γ₀),
    w = lampDiff β hβ ((g * iotaVertical β hβ γ) • tSite β hβ)
      (g • tSite β hβ) k}

/-- **The first-stage radical.**  The normal subgroup generated by all
base-move lamp differences: the part of the lamp base that the first collapse
stage makes invisible. -/
def stageRadical (k : K₀) : Subgroup (WreathV (K := K₀) β hβ) :=
  Subgroup.normalClosure (baseMoveSet β hβ k)

instance stageRadical_normal (k : K₀) : (stageRadical β hβ k).Normal :=
  Subgroup.normalClosure_normal

include hβ in
/-- **Sections 37 and 47, the inclusion.**  The first-stage radical lies in the
literal MF radical.  Property `(T)` of the base and the HNN relation are the
only inputs; no analytic hypothesis remains. -/
theorem stageRadical_le_actualCoronaMFResidual
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k : K₀} (hk2 : k * k = 1) :
    stageRadical β hβ k ≤ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  refine le_trans ?_ (involutiveCollapseDefect_le_actualCoronaMFResidual
    (baseSub_hasKazhdanPropertyT β hβ hΓ) (fun _ hw => wreathT_compress β hβ hw))
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨g, γ, rfl⟩
  exact lampDiff_mem_defect β hβ hk2 g γ

include hβ in
/-- **Properness makes the invisible part nontrivial.**  An element outside the
image of the self-embedding gives a base move that really separates two sites,
so the first-stage radical is not trivial. -/
theorem stageRadical_ne_bot {k : K₀} (hk₀ : k ≠ 1) {a₀ : Γ₀}
    (ha₀ : a₀ ∉ Set.range β) :
    stageRadical β hβ k ≠ ⊥ := by
  intro hbot
  have hmem : lampDiff β hβ (iotaVertical β hβ a₀ • tSite β hβ)
      (tSite β hβ) k ∈ stageRadical β hβ k := by
    refine Subgroup.subset_normalClosure ⟨1, a₀, ?_⟩
    rw [one_mul, one_smul]
  rw [hbot, Subgroup.mem_bot] at hmem
  exact commutator_witnessLamp_ne_one β hβ hk₀ ha₀
    ((commutator_eq_lampDiff β hβ a₀ k).trans hmem)

include hβ in
/-- **The exact radical of the first stage.**  When the first-stage quotient is
MF, the literal MF radical of the wreath product is exactly the first-stage
radical: the inclusion above is an equality. -/
theorem actualCoronaMFResidual_eq_stageRadical
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k : K₀} (hk2 : k * k = 1)
    (hquot : IsCDEOperatorMF (WreathV (K := K₀) β hβ ⧸ stageRadical β hβ k)) :
    actualCoronaMFResidual (WreathV (K := K₀) β hβ) = stageRadical β hβ k :=
  actualCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF _
    (stageRadical_le_actualCoronaMFResidual β hβ hΓ hk2) hquot

end MarkedCompression
end GroupApproximation
