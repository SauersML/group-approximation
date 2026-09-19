import GroupApproximation.Sofic.InfranormalCompressionPair
import GroupApproximation.Sofic.MFNonsoficDoubleEndpoint
import GroupApproximation.Sofic.SoficPositiveControl
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The centralizer-normalization input cannot be discharged

`Sofic.MFNonsoficDoubleEndpoint.HasSoficCentralizerNormalization Γ` is the
Kun--Thom conclusion the double construction consumes: in every faithful
permutation-ultraproduct representation of `G`, the centralizer of `Γ` is
normalized by `G`.  It is carried as a hypothesis, and
`metadata/LITERATURE_QUARANTINE.md` lists the datum that bundles it.

**It is not a lemma waiting to be proved.  It is false.**  This file proves
that, and locates exactly why the Kun--Thom theorem is not contradicted.

## The shadow

Soficity of `G` alone turns the property into a statement with no analysis in
it.  Feed it `q = ρ γ₀` for a `γ₀ ∈ Γ` that centralizes `Γ`: the hypothesis is
then automatic, and faithfulness of `ρ` pushes the conclusion back down to `G`.
What comes out (`commute_conj_of_hasSoficCentralizerNormalization`) is

```text
∀ γ₀ ∈ Γ centralizing Γ, ∀ g ∈ G, ∀ γ ∈ Γ,   g γ₀ g⁻¹  commutes with  γ.
```

For an abelian `Γ` that says every `G`-conjugate of `Γ` centralizes `Γ` — a
strong and easily violated condition.

## The counterexample

`Γ = ⟨s⟩` inside the dihedral group of order six.  `Γ` is abelian of order two,
`r s r⁻¹` is the other reflection, and two distinct reflections of a triangle do
not commute.  `not_hasSoficCentralizerNormalization_dihedral` is that
computation.

## Why Kun--Thom is untouched

Their hypothesis is that `Γ` is **infranormal** and not normal.  Here the
counterexample's `Γ` is finite, and `isInfranormal_iff_normal_of_finite`
(in `Sofic/InfranormalCompressionPair`) proves that a *finite* subgroup is
infranormal exactly when it is normal.  So no finite subgroup can be a
compression pair at all: the peripheral subgroup of a genuine Kun--Thom pair is
infinite, and the counterexample is nowhere near their hypothesis.

The consequence for the quarantine is exact.  The centralizer-normalization row
is not "an input we have not got round to proving".  It is an input that
**must** be assumed, because the unrestricted statement is refuted here; only a
theorem carrying property (T) and infranormality can supply it.
-/

namespace GroupApproximation

/-! ## The group-theoretic shadow of the property -/

/-- **What centralizer normalization says about a sofic group.**  No ultrafilter
survives in the conclusion: for a sofic `G`, the property forces every
`G`-conjugate of a `Γ`-centralizing element of `Γ` to centralize `Γ` again. -/
theorem commute_conj_of_hasSoficCentralizerNormalization {G : Type} [Group G]
    [Countable G] {Γ : Subgroup G} (h : HasSoficCentralizerNormalization Γ)
    (hsofic : IsSofic G) {γ₀ : G} (hcentral : ∀ γ ∈ Γ, Commute γ₀ γ)
    (g : G) {γ : G} (hγ : γ ∈ Γ) : Commute (g * γ₀ * g⁻¹) γ := by
  obtain ⟨S⟩ := (isSofic_iff_nonempty_soficApproximation G).mp hsofic
  let 𝒰 : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have h𝒰 : (𝒰 : Filter ℕ) ≤ Filter.cofinite := Ultrafilter.of_le _
  obtain ⟨ι, hι⟩ := exists_soficEmbedding_of_soficApproximation S h𝒰
  have hq : ∀ δ : G, δ ∈ Γ → Commute (ι γ₀) (ι δ) :=
    fun δ hδ ↦ (hcentral δ hδ).map ι
  have hcomm := h 𝒰 S.model ι hι (ι γ₀) hq g γ hγ
  have hrw : ι g * ι γ₀ * (ι g)⁻¹ = ι (g * γ₀ * g⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [hrw] at hcomm
  have hkey : (g * γ₀ * g⁻¹) * γ = γ * (g * γ₀ * g⁻¹) := by
    apply hι
    have hc := hcomm.eq
    simp only [map_mul] at hc ⊢
    exact hc
  exact hkey

/-! ## The refutation -/

open DihedralGroup

/-- The reflection subgroup of the dihedral group of order six. -/
abbrev refl3 : Subgroup (DihedralGroup 3) :=
  Subgroup.zpowers (DihedralGroup.sr (0 : ZMod 3))

theorem sr_zero_mem_refl3 : DihedralGroup.sr (0 : ZMod 3) ∈ refl3 :=
  Subgroup.mem_zpowers _

theorem commute_sr_zero_of_mem_refl3 :
    ∀ γ ∈ refl3, Commute (DihedralGroup.sr (0 : ZMod 3)) γ := by
  intro γ hγ
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hγ
  exact (Commute.refl (DihedralGroup.sr (0 : ZMod 3))).zpow_right n

/-- The rotated reflection does not commute with the original one. -/
theorem not_commute_rotated_refl :
    ¬ Commute (DihedralGroup.r (1 : ZMod 3) * DihedralGroup.sr (0 : ZMod 3)
        * (DihedralGroup.r (1 : ZMod 3))⁻¹) (DihedralGroup.sr (0 : ZMod 3)) := by
  intro hcomm
  have h := hcomm.eq
  revert h
  decide

/-- **The centralizer-normalization property is false.**  The reflection
subgroup of the dihedral group of order six refutes it. -/
theorem not_hasSoficCentralizerNormalization_dihedral :
    ¬ HasSoficCentralizerNormalization refl3 := by
  intro h
  exact not_commute_rotated_refl
    (commute_conj_of_hasSoficCentralizerNormalization h
      (isSofic_of_finite' (DihedralGroup 3)) commute_sr_zero_of_mem_refl3
      (DihedralGroup.r (1 : ZMod 3)) sr_zero_mem_refl3)

/-- The property is therefore not a theorem of group theory: there is a group
and a subgroup for which it fails. -/
theorem exists_not_hasSoficCentralizerNormalization :
    ∃ (G : Type) (_ : Group G) (Γ : Subgroup G),
      ¬ HasSoficCentralizerNormalization Γ :=
  ⟨DihedralGroup 3, inferInstance, refl3,
    not_hasSoficCentralizerNormalization_dihedral⟩

/-! ## Why this leaves the Kun--Thom theorem alone -/

/-- The refuting pair is not a compression pair: its peripheral subgroup is
finite, and a finite infranormal subgroup is normal. -/
theorem refl3_not_isCompressionPair : ¬ IsCompressionPair refl3 :=
  fun h ↦ h.not_finite Subtype.finite

end GroupApproximation
