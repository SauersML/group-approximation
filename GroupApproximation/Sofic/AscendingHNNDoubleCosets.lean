import GroupApproximation.Sofic.AscendingHNNStabilizer

/-!
# Height separates the double cosets of the ascending-HNN base

**Lemma 54.4** of the dossier, the group-theoretic half of the
non-finite-presentability obstruction.

Diagonal orbits of `G` on `(G/Γ)²` correspond to double cosets `Γ \ G / Γ`:
translate the first coordinate to the base point and the residual stabiliser
`Γ` acts on the second.  For an ascending HNN extension the height
homomorphism is constant on a double coset, and `Γ tⁿ Γ` has height `n`, so
there are infinitely many of them.

That is exactly the input Cornulier's finite-presentation criterion for
permutational wreath products rules out: a finitely presented transitive
wreath product with finitely generated point stabiliser can only have finitely
many diagonal orbits.  The graph-product half of the argument is not
formalized here; this file supplies the arithmetic that makes it bite.
-/

namespace GroupApproximation
namespace MarkedCompression

open MappingTelescope SemidirectProduct

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-! ## The height homomorphism -/

/-- The height of the ascending-HNN model: the semidirect-product projection. -/
abbrev height : Vertical α hα →* Multiplicative ℤ := rightHom

/-- The base copy has height zero. -/
theorem height_iotaVertical (γ : Γ) : height α hα (iotaVertical α hα γ) = 1 := by
  show rightHom (inl (level α hα 0 γ) : Vertical α hα) = 1
  exact rightHom_inl _

/-- Every element of the base copy has height zero. -/
theorem height_eq_one_of_mem_range {v : Vertical α hα}
    (hv : v ∈ (iotaVertical α hα).range) : height α hα v = 1 := by
  obtain ⟨γ, rfl⟩ := hv
  exact height_iotaVertical α hα γ

/-- The stable letter has height one. -/
theorem height_tVertical : height α hα (tVertical α hα) = Multiplicative.ofAdd 1 :=
  rightHom_inr _

/-- The stable letter's powers realise every height. -/
theorem toAdd_height_tVertical_zpow (n : ℤ) :
    Multiplicative.toAdd (height α hα (tVertical α hα ^ n)) = n := by
  rw [map_zpow, height_tVertical]
  simp

/-! ## Height is constant on a double coset -/

/-- Membership in the base copy, read off a coset equation. -/
theorem mem_range_of_smul_rootCoset_eq {v : Vertical α hα}
    (h : v • rootCoset α hα = rootCoset α hα) :
    v ∈ (iotaVertical α hα).range := by
  rw [smul_rootCoset] at h
  show v ∈ (iotaVertical α hα).range
  have h' : (QuotientGroup.mk v : Cosets α hα) = QuotientGroup.mk 1 := h
  rw [QuotientGroup.eq] at h'
  have : v⁻¹ ∈ (iotaVertical α hα).range := by simpa using h'
  simpa using Subgroup.inv_mem _ this

/-- **Lemma 54.4.**  No element of the group carries the pair
`(Γ, tᵐ Γ)` to the pair `(Γ, tⁿ Γ)` unless `m = n`: the first coordinate
forces height zero, and then the second coordinate reads off `m = n`. -/
theorem no_diagonal_transport {m n : ℤ} (hmn : m ≠ n) (g : Vertical α hα)
    (h1 : g • rootCoset α hα = rootCoset α hα) :
    g • ((tVertical α hα ^ m) • rootCoset α hα)
      ≠ (tVertical α hα ^ n) • rootCoset α hα := by
  intro h2
  have hg : height α hα g = 1 :=
    height_eq_one_of_mem_range α hα (mem_range_of_smul_rootCoset_eq α hα h1)
  rw [← mul_smul, smul_rootCoset, smul_rootCoset] at h2
  rw [QuotientGroup.eq] at h2
  have hheight :
      height α hα ((g * tVertical α hα ^ m)⁻¹ * tVertical α hα ^ n) = 1 :=
    height_eq_one_of_mem_range α hα h2
  have hexp : height α hα ((g * tVertical α hα ^ m)⁻¹ * tVertical α hα ^ n)
      = (height α hα (tVertical α hα ^ m))⁻¹
          * height α hα (tVertical α hα ^ n) := by
    rw [map_mul, map_inv, map_mul, hg, one_mul]
  rw [hheight] at hexp
  have hpow : height α hα (tVertical α hα ^ m)
      = height α hα (tVertical α hα ^ n) := inv_mul_eq_one.mp hexp.symm
  have hmn' : m = n := by
    have htoAdd := congrArg Multiplicative.toAdd hpow
    rwa [toAdd_height_tVertical_zpow α hα, toAdd_height_tVertical_zpow α hα]
      at htoAdd
  exact hmn hmn'

/-- The pairs `(Γ, tⁿ Γ)` lie in pairwise distinct diagonal orbits, so the
diagonal action on the square of the coset space has infinitely many orbits. -/
theorem injective_diagonal_orbit :
    Function.Injective fun n : ℤ =>
      MulAction.orbit (Vertical α hα)
        (rootCoset α hα, (tVertical α hα ^ n) • rootCoset α hα) := by
  intro m n hmn
  by_contra hne
  have hmn' : MulAction.orbit (Vertical α hα)
        (rootCoset α hα, (tVertical α hα ^ m) • rootCoset α hα)
      = MulAction.orbit (Vertical α hα)
        (rootCoset α hα, (tVertical α hα ^ n) • rootCoset α hα) := hmn
  have hmem : (rootCoset α hα, (tVertical α hα ^ n) • rootCoset α hα) ∈
      MulAction.orbit (Vertical α hα)
        (rootCoset α hα, (tVertical α hα ^ m) • rootCoset α hα) := by
    rw [hmn']
    exact MulAction.mem_orbit_self _
  obtain ⟨g, hg⟩ := hmem
  have hg1 : g • rootCoset α hα = rootCoset α hα := by
    have hfst := congrArg Prod.fst hg
    simpa using hfst
  have hg2 : g • ((tVertical α hα ^ m) • rootCoset α hα)
      = (tVertical α hα ^ n) • rootCoset α hα := by
    have hsnd := congrArg Prod.snd hg
    simpa using hsnd
  exact no_diagonal_transport α hα hne g hg1 hg2

end MarkedCompression
end GroupApproximation
