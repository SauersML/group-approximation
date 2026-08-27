import GroupApproximation.Sofic.InfranormalCompressionPair
import GroupApproximation.Sofic.MFNonsoficDoubleEndpoint
import GroupApproximation.Sofic.SymmetricDoubleCovering

/-!
# The Kun--Thom witness lives in the covering

The word the centralizer theorem kills is

```text
w = [t k t⁻¹, γ]   in   H_K = G *_Γ (Γ × K),
```

nontrivial as soon as `t⁻¹ γ t ∉ Γ` and `k ≠ 1`
(`Sofic/FreeLampReduction.lampWitness_ne_one`).  It is a commutator whose lamp
letters cancel, so the retraction `H_K → K` kills it: `w` lies in the
Bass--Serre covering `⋆_{Γ, k ∈ K} G`, not merely in `H_K`.

This file computes its preimage there explicitly.  Writing `⟨i⟩ g` for the
image of `g` at the vertex `i`, and

```text
u = ⟨1⟩t · (⟨k⟩t)⁻¹,
```

the preimage is

```text
w̃ = u · ⟨k⟩γ · u⁻¹ · (⟨1⟩γ)⁻¹,
```

a four-letter word in two vertices of the covering
(`iteratedToFreeLamp_iteratedWitness`).  It is nontrivial exactly when `w` is,
because the covering map is injective.

At `K = C₂` the covering *is* the symmetric double
(`Sofic/SymmetricDoubleCovering`), so `w̃` becomes a named nontrivial element
`doubleWitness` of `G *_Γ G`.  That is what makes the obstruction a statement
about the double itself rather than about the auxiliary lamp group: the whole
Kun--Thom mechanism is the assertion that no sofic approximation of `G *_Γ G`
survives conjugation of `doubleWitness`.

Everything here is unconditional.
-/

namespace GroupApproximation

open Monoid

/-! ## The witness in the `K`-fold covering -/

/-- The compressed vertex displacement: the vertex-`1` copy of the compressor
against its vertex-`k` copy. -/
def iteratedDisplacement (G : Type) [Group G] (Γ : Subgroup G) (K : Type)
    [Group K] (t : G) (k : K) : IteratedDouble G Γ K :=
  inIterated G Γ K 1 t * (inIterated G Γ K k t)⁻¹

/-- **The Kun--Thom witness, read in the covering.** -/
def iteratedWitness (G : Type) [Group G] (Γ : Subgroup G) (K : Type) [Group K]
    (t γ : G) (k : K) : IteratedDouble G Γ K :=
  iteratedDisplacement G Γ K t k * inIterated G Γ K k γ
    * (iteratedDisplacement G Γ K t k)⁻¹ * (inIterated G Γ K 1 γ)⁻¹

theorem iteratedToFreeLamp_iteratedDisplacement (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] (t : G) (k : K) :
    iteratedToFreeLamp G Γ K (iteratedDisplacement G Γ K t k)
      = inAmbient G Γ K t * inLamp G Γ K k * (inAmbient G Γ K t)⁻¹
        * (inLamp G Γ K k)⁻¹ := by
  simp only [iteratedDisplacement, map_mul, map_inv,
    iteratedToFreeLamp_inIterated, map_one, one_mul, inv_one, mul_one]
  group

/-- **The covering map carries `w̃` to the witness.** -/
theorem iteratedToFreeLamp_iteratedWitness (G : Type) [Group G]
    (Γ : Subgroup G) (K : Type) [Group K] (t γ : G) (k : K) :
    iteratedToFreeLamp G Γ K (iteratedWitness G Γ K t γ k)
      = lampWitness G Γ K t γ k := by
  simp only [iteratedWitness, lampWitness, iteratedDisplacement, map_mul,
    map_inv, iteratedToFreeLamp_inIterated, map_one, one_mul, inv_one, mul_one]
  group

/-- The witness lies in the Bass--Serre covering, not merely in the amalgam. -/
theorem lampWitness_mem_lampKernel (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (t γ : G) (k : K) :
    lampWitness G Γ K t γ k ∈ lampKernel G Γ K := by
  rw [← iteratedToFreeLamp_iteratedWitness]
  exact MonoidHom.mem_ker.mpr
    (lampRetraction_iteratedToFreeLamp G Γ K
      (iteratedWitness G Γ K t γ k))

/-- The retraction kills the witness. -/
theorem lampRetraction_lampWitness (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] (t γ : G) (k : K) :
    lampRetraction G Γ K (lampWitness G Γ K t γ k) = 1 :=
  MonoidHom.mem_ker.mp (lampWitness_mem_lampKernel G Γ K t γ k)

/-- **The preimage is nontrivial.**  Escaping the peripheral subgroup makes the
covering carry a nontrivial four-letter word on two of its vertices. -/
theorem iteratedWitness_ne_one (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] {t γ : G} (hesc : t⁻¹ * γ * t ∉ Γ) {k : K}
    (hk : k ≠ 1) : iteratedWitness G Γ K t γ k ≠ 1 := by
  intro hcon
  refine lampWitness_ne_one G Γ K hesc hk ?_
  rw [← iteratedToFreeLamp_iteratedWitness, hcon, map_one]

/-! ## The witness in the symmetric double -/

/-- **The Kun--Thom obstruction, as an element of `G *_Γ G`.**  The order-two
covering is the symmetric double, so the witness is a word there. -/
noncomputable def doubleWitness (G : Type) [Group G] (Γ : Subgroup G)
    (t γ : G) : SymmetricDouble G Γ :=
  (symmetricDoubleEquivIteratedFlip G Γ).symm
    (iteratedWitness G Γ FlipC2 t γ FlipC2.swap)

@[simp] theorem symmetricDoubleEquivIteratedFlip_doubleWitness (G : Type)
    [Group G] (Γ : Subgroup G) (t γ : G) :
    symmetricDoubleEquivIteratedFlip G Γ (doubleWitness G Γ t γ)
      = iteratedWitness G Γ FlipC2 t γ FlipC2.swap :=
  (symmetricDoubleEquivIteratedFlip G Γ).apply_symm_apply _

/-- **The obstruction is a nontrivial element of the symmetric double.** -/
theorem doubleWitness_ne_one (G : Type) [Group G] (Γ : Subgroup G)
    {t γ : G} (hesc : t⁻¹ * γ * t ∉ Γ) : doubleWitness G Γ t γ ≠ 1 := by
  intro hcon
  refine iteratedWitness_ne_one G Γ FlipC2 hesc flipC2_swap_ne_one ?_
  rw [← symmetricDoubleEquivIteratedFlip_doubleWitness G Γ t γ, hcon, map_one]

/-- Non-normality alone produces a nontrivial witness in the double. -/
theorem exists_doubleWitness_ne_one (G : Type) [Group G] (Γ : Subgroup G)
    (hnn : ¬ Γ.Normal) :
    ∃ t γ : G, γ ∈ Γ ∧ doubleWitness G Γ t γ ≠ 1 := by
  obtain ⟨t, γ, hγ, hesc⟩ := exists_escape_of_not_normal hnn
  exact ⟨t, γ, hγ, doubleWitness_ne_one G Γ hesc⟩

end GroupApproximation
