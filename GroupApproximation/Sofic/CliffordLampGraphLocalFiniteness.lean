import GroupApproximation.Sofic.LiteralBlockNormalForm
import GroupApproximation.Sofic.LocallyFiniteMF
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The lamp factor of the orbital graph is *not* locally finite

`Sofic.CliffordLampPermanence` proves `IsLocallyFiniteGroup (CliffordLamp X)`,
and it is natural to expect the same for `LiteralBlockNormalForm.LampFactor`,
the Clifford group `C(𝒢)` of the orbital graph.  **It is false**, and this
module says why in a checkable way.

The generic tool, `isLocallyFiniteGroup_of_central_involution`, asks that the
commutator of *every* pair of generators lie in the central `⟨ζ⟩`:

    hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z

For `CliffordLamp X` that hypothesis holds, because `commutator_lamp_lamp`
braids *every* distinct pair of lamps: its graph is complete.  For `LampFactor`
it fails.  `IsLampRelator.braiding` imposes `⁅c_ξ, c_η⁆ = ζ` **only along the
edges** of `𝒢`, which is the `V`-orbit of the single pair `{τo, v₁τo}`; between
two non-adjacent sites the presentation imposes *nothing at all*.  Two
involutions with no relation between them generate an infinite dihedral group,
so the lamp factor has a two-generated infinite subgroup.

This is not an artifact of the formalization.  `LiteralBlockNormalForm`'s own
module docstring describes `C(𝒢)` as an amalgamated free product
`∗_{⟨ζ⟩} P_i` over the connected pieces of `𝒢`, and a nontrivial amalgam of
that shape is never locally finite --- even when every piece is a finite
clique, a free product of two finite groups over a common `ℤ/2` is infinite.

## What is proved here, and what it is conditional on

`LiteralBlockNormalForm` deliberately proves nothing about the geometry of
`𝒢` (its docstring: "Nothing about the isomorphism type of `B`, the
injectivity of the doubling endomorphism, or the geometry of `𝒢` enters"), so
the *existence* of a non-adjacent pair is not available here either.  The
refutation is therefore stated as an implication, with the geometric input
isolated as its hypothesis:

* `not_isLocallyFiniteGroup_lampFactor` --- two distinct non-adjacent sites
  make `LampFactor` fail local finiteness;
* `not_isLocallyFiniteGroup_lampFactor_of_two_blocks` --- the same conclusion
  from two sites in *different blocks*, which is the repository's own
  vocabulary: `blockOf_eq_of_adjacent` says adjacent sites share a block, so
  distinct blocks give non-adjacency for free.

The witness is the map that sends `ζ` and every lamp to `1` except the two
chosen ones, which go to the reflections `sr 0` and `sr 1` of
`DihedralGroup 0`.  Every braiding relator survives because no edge joins the
two chosen sites, and `sr 0 * sr 1 = r 1` has infinite order.
-/

namespace GroupApproximation
namespace CliffordLampGraph

open LiteralBlockNormalForm
open scoped commutatorElement

noncomputable section

/-! ## The two-reflection test map -/

/-- The lamp assignment behind the refutation: `1` everywhere except at two
chosen sites, which receive the two reflections generating the infinite
dihedral group. -/
def twoLamp (ξ η : Site) : Site → DihedralGroup 0 :=
  letI : DecidableEq Site := Classical.decEq Site
  fun σ => if σ = ξ then DihedralGroup.sr 0
    else if σ = η then DihedralGroup.sr 1 else 1

theorem twoLamp_left (ξ η : Site) : twoLamp ξ η ξ = DihedralGroup.sr 0 := by
  letI : DecidableEq Site := Classical.decEq Site
  show (if ξ = ξ then DihedralGroup.sr 0
    else if ξ = η then DihedralGroup.sr 1 else 1) = _
  rw [if_pos rfl]

theorem twoLamp_right {ξ η : Site} (hne : η ≠ ξ) :
    twoLamp ξ η η = DihedralGroup.sr 1 := by
  letI : DecidableEq Site := Classical.decEq Site
  show (if η = ξ then DihedralGroup.sr 0
    else if η = η then DihedralGroup.sr 1 else 1) = _
  rw [if_neg hne, if_pos rfl]

theorem twoLamp_other {ξ η σ : Site} (h1 : σ ≠ ξ) (h2 : σ ≠ η) :
    twoLamp ξ η σ = 1 := by
  letI : DecidableEq Site := Classical.decEq Site
  show (if σ = ξ then DihedralGroup.sr 0
    else if σ = η then DihedralGroup.sr 1 else 1) = _
  rw [if_neg h1, if_neg h2]

theorem twoLamp_sq (ξ η σ : Site) : twoLamp ξ η σ ^ 2 = 1 := by
  letI : DecidableEq Site := Classical.decEq Site
  have hsr : ∀ i : ZMod 0, (DihedralGroup.sr i) ^ 2 = 1 := by
    intro i
    rw [pow_two, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]
  show (if σ = ξ then DihedralGroup.sr 0
    else if σ = η then DihedralGroup.sr 1 else 1) ^ 2 = 1
  by_cases h1 : σ = ξ
  · rw [if_pos h1]; exact hsr 0
  · rw [if_neg h1]
    by_cases h2 : σ = η
    · rw [if_pos h2]; exact hsr 1
    · rw [if_neg h2, one_pow]

/-- **The test homomorphism.**  Two non-adjacent sites carry the two
reflections; the sign and every other lamp die.  Every braiding relator holds
because no edge of `𝒢` joins the two chosen sites. -/
def twoLampLift {ξ η : Site} (hne : ¬ Adjacent ξ η) :
    LampFactor →* DihedralGroup 0 :=
  lampLift (1 : DihedralGroup 0) (twoLamp ξ η) (one_pow 2) (twoLamp_sq ξ η)
    (fun _ => Commute.one_left _)
    (by
      intro a b hab
      rcases eq_or_ne a ξ with rfl | haξ
      · rcases eq_or_ne b a with rfl | hba
        · exact commutatorElement_self _
        · rcases eq_or_ne b η with rfl | hbη
          · exact absurd hab hne
          · rw [twoLamp_other hba hbη]
            exact commutatorElement_one_right _
      · rcases eq_or_ne a η with rfl | haη
        · rcases eq_or_ne b ξ with rfl | hbξ
          · exact absurd hab.flip hne
          · rcases eq_or_ne b a with rfl | hba
            · exact commutatorElement_self _
            · rw [twoLamp_other hbξ hba]
              exact commutatorElement_one_right _
        · rw [twoLamp_other haξ haη]
          exact commutatorElement_one_left _)

theorem twoLampLift_left {ξ η : Site} (hne : ¬ Adjacent ξ η) :
    twoLampLift hne (lampAt ξ) = DihedralGroup.sr 0 := by
  rw [twoLampLift, lampLift_at, twoLamp_left]

theorem twoLampLift_right {ξ η : Site} (hne : ¬ Adjacent ξ η)
    (hd : η ≠ ξ) :
    twoLampLift hne (lampAt η) = DihedralGroup.sr 1 := by
  rw [twoLampLift, lampLift_at, twoLamp_right hd]

/-- The product of the two marked lamps has infinite order downstairs: it is
the rotation `r 1` of the infinite dihedral group. -/
theorem twoLampLift_mul {ξ η : Site} (hne : ¬ Adjacent ξ η) (hd : η ≠ ξ) :
    twoLampLift hne (lampAt ξ * lampAt η) = DihedralGroup.r 1 := by
  rw [map_mul, twoLampLift_left, twoLampLift_right hne hd,
    DihedralGroup.sr_mul_sr, sub_zero]

/-! ## The refutation -/

/-- **The lamp factor of the orbital graph is not locally finite.**  Two
distinct non-adjacent sites carry lamps that generate an infinite dihedral
group, so no finite subgroup contains them both.

Contrast `CliffordLamp.isLocallyFiniteGroup_cliffordLamp`, which holds because
*every* distinct pair of lamps braids there.  The difference is exactly the
hypothesis `hcomm` of `isLocallyFiniteGroup_of_central_involution`, which
quantifies over all pairs of generators and which `IsLampRelator.braiding`
supplies only along edges. -/
theorem not_isLocallyFiniteGroup_lampFactor {ξ η : Site} (hd : η ≠ ξ)
    (hne : ¬ Adjacent ξ η) : ¬ IsLocallyFiniteGroup LampFactor := by
  classical
  intro hloc
  obtain ⟨H, hHfin, hmem⟩ := hloc {lampAt ξ, lampAt η}
  haveI : Finite H := hHfin
  have hxH : lampAt ξ ∈ H := hmem _ (by simp)
  have hyH : lampAt η ∈ H := hmem _ (by simp)
  obtain ⟨z, hz⟩ : ∃ z : H, (z : LampFactor) = lampAt ξ * lampAt η :=
    ⟨⟨lampAt ξ * lampAt η, H.mul_mem hxH hyH⟩, rfl⟩
  have hpow : ∀ k : ℕ, twoLampLift hne ((z ^ k : H) : LampFactor)
      = DihedralGroup.r (k : ZMod 0) := by
    intro k
    rw [Subgroup.coe_pow, hz, map_pow, twoLampLift_mul hne hd,
      DihedralGroup.r_one_pow]
  have hinj : Function.Injective (fun k : ℕ => (z ^ k : H)) := by
    intro a b hab
    -- `hab` is a beta-redex `(fun k ↦ z ^ k) a = …`, which `rw` cannot match;
    -- retyping it contracts the redex.
    have hab' : (z : H) ^ a = (z : H) ^ b := hab
    have h : DihedralGroup.r ((a : ℕ) : ZMod 0)
        = DihedralGroup.r ((b : ℕ) : ZMod 0) := by
      rw [← hpow a, ← hpow b, hab']
    simpa using h
  exact absurd hinj (not_injective_infinite_finite _)

/-- The same conclusion from the fibration the soficity tower already uses:
two sites in different blocks are non-adjacent, because
`blockOf_eq_of_adjacent` says adjacent sites share a block. -/
theorem not_isLocallyFiniteGroup_lampFactor_of_two_blocks {ξ η : Site}
    (hb : blockOf ξ ≠ blockOf η) : ¬ IsLocallyFiniteGroup LampFactor := by
  -- the sites are invisible in the conclusion, so they must be named
  refine not_isLocallyFiniteGroup_lampFactor (ξ := ξ) (η := η)
    (fun hd => hb ?_) (fun hadj => hb ?_)
  · rw [hd]
  · exact blockOf_eq_of_adjacent hadj

end

end CliffordLampGraph
end GroupApproximation
