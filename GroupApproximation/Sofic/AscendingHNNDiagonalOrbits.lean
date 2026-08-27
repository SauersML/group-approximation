import GroupApproximation.Sofic.AscendingHNNFolner

/-!
# Lemma 54.4: the coset square of an ascending HNN extension has infinitely many orbits

Diagonal orbits on the square of a transitive coset space are classified by double
cosets, and in an ascending HNN extension the height homomorphism separates the
double cosets of the powers of the stable letter: every element of `Γ tⁿ Γ` has
height `n`.  Concretely, the pairs `(x₀, x_n)` taken from the ray of Section 10
lie in pairwise distinct diagonal orbits, so the orbit space is infinite.

This is the geometric input of Theorem 54.5: a finitely presented transitive
permutational wreath product would force finitely many diagonal orbits, and the
height family of double cosets rules that out.
-/

namespace GroupApproximation

namespace AscendingHNNFolner

open MappingTelescope MarkedCompression SemidirectProduct

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- An element fixing the base point of the ray lies in the base copy, hence has
height zero. -/
theorem right_eq_one_of_smul_ray_zero {g : Vertical α hα}
    (hg : g • ray α hα 0 = ray α hα 0) : g.right = 1 := by
  have h1 : g • (QuotientGroup.mk ((tVertical α hα) ^ (-(0 : ℤ)))
      : Cosets α hα) = QuotientGroup.mk ((tVertical α hα) ^ (-(0 : ℤ))) := hg
  rw [MulAction.Quotient.smul_mk, smul_eq_mul] at h1
  obtain ⟨γ, hγ⟩ := (QuotientGroup.eq (s := (iotaVertical α hα).range)).mp h1
  have hr := congrArg SemidirectProduct.right hγ
  rw [right_iotaVertical] at hr
  have hcalc : ((g * (tVertical α hα) ^ (-(0 : ℤ)))⁻¹
      * (tVertical α hα) ^ (-(0 : ℤ))).right = (g.right)⁻¹ := by
    simp [SemidirectProduct.inv_right]
  rw [hcalc] at hr
  simpa using (congrArg (fun z : Multiplicative ℤ => z⁻¹) hr).symm

/-- **Lemma 54.4.**  Distinct ray points give distinct diagonal orbits: no group
element fixing the base point carries one ray point to another. -/
theorem ray_pair_orbit_ne {m n : ℤ} (hmn : m ≠ n) (g : Vertical α hα)
    (hzero : g • ray α hα 0 = ray α hα 0) : g • ray α hα m ≠ ray α hα n := by
  intro hg
  have hright : g.right = 1 := right_eq_one_of_smul_ray_zero α hα hzero
  have h1 : g • (QuotientGroup.mk ((tVertical α hα) ^ (-m)) : Cosets α hα)
      = QuotientGroup.mk ((tVertical α hα) ^ (-n)) := hg
  rw [MulAction.Quotient.smul_mk, smul_eq_mul] at h1
  obtain ⟨γ, hγ⟩ := (QuotientGroup.eq (s := (iotaVertical α hα).range)).mp h1
  have hr := congrArg SemidirectProduct.right hγ
  rw [right_iotaVertical] at hr
  have hcalc : ((g * (tVertical α hα) ^ (-m))⁻¹
      * (tVertical α hα) ^ (-n)).right = Multiplicative.ofAdd (m - n) := by
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      right_tVertical_zpow, hright]
    rw [one_mul, ← ofAdd_neg, ← ofAdd_add]
    congr 1
    ring
  rw [hcalc] at hr
  have hzero' : m - n = 0 := by
    simpa using congrArg Multiplicative.toAdd hr.symm
  omega

/-- The diagonal orbit of a ray pair determines its index: the assignment
`n ↦ orbit of (x₀, x_n)` is injective, so the diagonal orbit space of the coset
square is infinite. -/
theorem orbit_ray_pair_injective :
    Function.Injective fun n : ℤ =>
      MulAction.orbit (Vertical α hα) (ray α hα 0, ray α hα n) := by
  intro m n hmn
  by_contra hne
  have hmem : (ray α hα 0, ray α hα n)
      ∈ MulAction.orbit (Vertical α hα) (ray α hα 0, ray α hα m) := by
    have hself : (ray α hα 0, ray α hα n)
        ∈ MulAction.orbit (Vertical α hα) (ray α hα 0, ray α hα n) :=
      MulAction.mem_orbit_self _
    simpa only [hmn] using hself
  obtain ⟨g, hg⟩ := hmem
  have hfst : g • ray α hα 0 = ray α hα 0 := congrArg Prod.fst hg
  have hsnd : g • ray α hα m = ray α hα n := congrArg Prod.snd hg
  exact ray_pair_orbit_ne α hα hne g hfst hsnd

end AscendingHNNFolner

end GroupApproximation
