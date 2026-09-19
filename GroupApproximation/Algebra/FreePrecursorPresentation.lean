import GroupApproximation.Algebra.FreePrecursorUniversal
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# Equation (54.17): the precursor is the free product modulo the stabiliser
# relations

`Algebra/FreePrecursorUniversal` proves that a homomorphism out of the free
precursor `E = (∗_{x ∈ G/Γ} K_x) ⋊ G` is exactly a pair `(φ, ψ)` with
`φ(Γ)` centralising `ψ(K)`.  That is a description of `E` by a universal
property; (54.17) is the same description as a presentation.  This file turns
one into the other.

The presented object is the free product `K ∗ G` modulo the normal closure of

  `⁅u, k⁆`  for `u ∈ Γ` and `k ∈ K`,

which is exactly the relator family `[u, a] = 1` of (54.17) before choosing
generating sets for `Γ` and `K`.  Nothing else is imposed: the relations of `G`
and of `K` are already carried by the two factors of the free product.

## Why the two agree

Both receive the same maps.  A homomorphism out of `K ∗ G` is a pair `(ψ, φ)`
with no condition, and killing the displayed commutators is precisely the
condition that `φ(Γ)` centralises `ψ(K)` -- so maps out of the quotient are
pairs satisfying that condition, which by `precursorLift` and
`precursorLift_unique` is what maps out of `E` are.  Two groups with the same
universal property are isomorphic, and `presEquiv` is the isomorphism, built by
running each universal property against the other and checking the composites on
generators.

The base site does the work in one direction: `Γ` stabilises the coset of `1`,
so conjugating the base lamp by `u ∈ Γ` returns it, which is why the relators die
in `E`.

## What is not here

The finiteness reading of (54.17) -- that `E` is finitely presented when `K` and
`G` are and `Γ` is finitely generated -- does not follow from the isomorphism
alone.  It additionally needs `K ∗ G` to be finitely presented, which Mathlib
does not provide for coproducts (only for products), and the relator set to be
finitely normally generated, which needs generating sets for `Γ` and `K`.  Both
are presentation bookkeeping on top of the isomorphism proved here.
-/

namespace GroupApproximation

namespace FreePrecursor

universe u w

open Monoid

open scoped commutatorElement

variable {K : Type u} [Group K] {G : Type w} [Group G]

/-! ## The presented group -/

/-- The relators of (54.17): the stabiliser commutes with the base lamp. -/
def presRelators (Γ : Subgroup G) : Set (Coprod K G) :=
  {z | ∃ u ∈ Γ, ∃ k : K,
    z = ⁅(Coprod.inr u : Coprod K G), (Coprod.inl k : Coprod K G)⁆}

/-- The normal closure of the stabiliser relations. -/
def presNormal (Γ : Subgroup G) : Subgroup (Coprod K G) :=
  Subgroup.normalClosure (presRelators Γ)

instance presNormal_normal (K : Type u) [Group K] (Γ : Subgroup G) :
    (presNormal (K := K) Γ).Normal :=
  Subgroup.normalClosure_normal

/-- The group presented by (54.17). -/
abbrev Pres (K : Type u) [Group K] {G : Type w} [Group G] (Γ : Subgroup G) :=
  Coprod K G ⧸ presNormal (K := K) Γ

variable (Γ : Subgroup G)

/-- The generators of the presented group: the base lamp. -/
def presK : K →* Pres K Γ :=
  (QuotientGroup.mk' (presNormal (K := K) Γ)).comp (Coprod.inl : K →* Coprod K G)

/-- The generators of the presented group: the acting group. -/
def presG : G →* Pres K Γ :=
  (QuotientGroup.mk' (presNormal (K := K) Γ)).comp (Coprod.inr : G →* Coprod K G)

/-- In the presented group the stabiliser commutes with the base lamp -- this is
what the relators say. -/
theorem presG_commute (u : G) (hu : u ∈ Γ) (k : K) :
    presG Γ u * presK Γ k = presK Γ k * presG Γ u := by
  have hmem : ⁅(Coprod.inr u : Coprod K G), (Coprod.inl k : Coprod K G)⁆
      ∈ presNormal (K := K) Γ :=
    Subgroup.subset_normalClosure ⟨u, hu, k, rfl⟩
  have hone : (QuotientGroup.mk' (presNormal (K := K) Γ))
      ⁅(Coprod.inr u : Coprod K G), (Coprod.inl k : Coprod K G)⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_commutatorElement] at hone
  exact (commutatorElement_eq_one_iff_commute.mp hone)

/-! ## The two maps -/

/-- The base lamp of `E`, as a homomorphism from `K`. -/
def baseLamp : K →* FreeWreath K G (G ⧸ Γ) :=
  (SemidirectProduct.inl).comp
    (Monoid.CoprodI.of (M := fun _ : G ⧸ Γ => K)
      (i := (QuotientGroup.mk 1 : G ⧸ Γ)))

/-- The stabiliser fixes the base site, so it centralises the base lamp in
`E`. -/
theorem inr_commute_baseLamp (u : G) (hu : u ∈ Γ) (k : K) :
    (SemidirectProduct.inr u : FreeWreath K G (G ⧸ Γ)) * baseLamp Γ k
      = baseLamp Γ k * SemidirectProduct.inr u := by
  set X : FreeLamp K (G ⧸ Γ) :=
    Monoid.CoprodI.of (M := fun _ : G ⧸ Γ => K)
      (i := (QuotientGroup.mk 1 : G ⧸ Γ)) k with hX
  have hfix : u • (QuotientGroup.mk 1 : G ⧸ Γ) = QuotientGroup.mk 1 := by
    show (QuotientGroup.mk (u * 1) : G ⧸ Γ) = QuotientGroup.mk 1
    rw [mul_one, QuotientGroup.eq]
    simpa using Γ.inv_mem hu
  have haut : freeLampActionHom K (G ⧸ Γ) u X = X := by
    rw [hX, freeLampActionHom_apply, freeLampMap, Monoid.CoprodI.lift_of, hfix]
  have hconj := SemidirectProduct.inl_aut (φ := freeLampActionHom K (G ⧸ Γ)) u X
  rw [haut] at hconj
  rw [map_inv] at hconj
  have key : (SemidirectProduct.inr u : FreeWreath K G (G ⧸ Γ))
      * SemidirectProduct.inl X * (SemidirectProduct.inr u)⁻¹
      = SemidirectProduct.inl X := hconj.symm
  show (SemidirectProduct.inr u : FreeWreath K G (G ⧸ Γ)) * SemidirectProduct.inl X
    = SemidirectProduct.inl X * SemidirectProduct.inr u
  calc (SemidirectProduct.inr u : FreeWreath K G (G ⧸ Γ)) * SemidirectProduct.inl X
      = ((SemidirectProduct.inr u : FreeWreath K G (G ⧸ Γ))
          * SemidirectProduct.inl X * (SemidirectProduct.inr u)⁻¹)
          * SemidirectProduct.inr u := by group
    _ = SemidirectProduct.inl X * SemidirectProduct.inr u := by rw [key]

/-- `E → Pres`: run the universal property of `E` against the presented
group. -/
def toPres : FreeWreath K G (G ⧸ Γ) →* Pres K Γ :=
  precursorLift Γ (presG Γ) (presK Γ) (fun u hu k => presG_commute Γ u hu k)

/-- `Pres → E`: the free product maps by the two generator families, and the
relators die because the stabiliser fixes the base site. -/
def fromPres : Pres K Γ →* FreeWreath K G (G ⧸ Γ) :=
  QuotientGroup.lift _
    (Coprod.lift (baseLamp Γ) SemidirectProduct.inr)
    (Subgroup.normalClosure_le_normal (by
      rintro _ ⟨u, hu, k, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
        Coprod.lift_apply_inr, Coprod.lift_apply_inl,
        commutatorElement_eq_one_iff_commute]
      exact inr_commute_baseLamp Γ u hu k))


/-! ## The two maps are inverse -/

@[simp] theorem toPres_inr (g : G) :
    toPres Γ (SemidirectProduct.inr g : FreeWreath K G (G ⧸ Γ)) = presG Γ g :=
  precursorLift_inr Γ (presG Γ) (presK Γ) (fun u hu k => presG_commute Γ u hu k) g

@[simp] theorem toPres_baseLamp (k : K) :
    toPres Γ (baseLamp Γ k) = presK Γ k :=
  precursorLift_base Γ (presG Γ) (presK Γ)
    (fun u hu k => presG_commute Γ u hu k) k

@[simp] theorem fromPres_presG (g : G) :
    fromPres Γ (presG Γ g) = (SemidirectProduct.inr g : FreeWreath K G (G ⧸ Γ)) :=
  rfl

@[simp] theorem fromPres_presK (k : K) :
    fromPres Γ (presK Γ k) = baseLamp Γ k :=
  rfl

theorem fromPres_comp_toPres :
    (fromPres Γ).comp (toPres Γ) = MonoidHom.id (FreeWreath K G (G ⧸ Γ)) := by
  refine precursorLift_unique _ _ ?_ ?_
  · intro g
    show fromPres Γ (toPres Γ (SemidirectProduct.inr g)) = SemidirectProduct.inr g
    rw [toPres_inr, fromPres_presG]
  · intro k
    show fromPres Γ (toPres Γ (baseLamp Γ k)) = baseLamp Γ k
    rw [toPres_baseLamp, fromPres_presK]

theorem toPres_comp_fromPres :
    (toPres Γ).comp (fromPres Γ) = MonoidHom.id (Pres K Γ) := by
  have h : ((toPres Γ).comp (fromPres Γ)).comp
        (QuotientGroup.mk' (presNormal (K := K) Γ))
      = (MonoidHom.id (Pres K Γ)).comp
        (QuotientGroup.mk' (presNormal (K := K) Γ)) := by
    refine Coprod.hom_ext ?_ ?_
    · refine MonoidHom.ext fun k => ?_
      show toPres Γ (fromPres Γ (presK Γ k)) = presK Γ k
      rw [fromPres_presK, toPres_baseLamp]
    · refine MonoidHom.ext fun g => ?_
      show toPres Γ (fromPres Γ (presG Γ g)) = presG Γ g
      rw [fromPres_presG, toPres_inr]
  refine MonoidHom.ext fun z => ?_
  induction z using QuotientGroup.induction_on with
  | H c => exact congrArg (fun f : Coprod K G →* Pres K Γ => f c) h

/-- **Equation (54.17).**  The free precursor is the free product of the lamp
group and the acting group, modulo the relations saying that the stabiliser
commutes with the base lamp. -/
def presEquiv : Pres K Γ ≃* FreeWreath K G (G ⧸ Γ) :=
  MonoidHom.toMulEquiv (fromPres Γ) (toPres Γ)
    (toPres_comp_fromPres Γ) (fromPres_comp_toPres Γ)


end FreePrecursor

end GroupApproximation
