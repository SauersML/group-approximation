import GroupApproximation.Analysis.CStarSeparableFaithfulRepresentation

/-!
# `G`-C⋆-algebras, equivariant maps and a faithful representation

Lane TWWUCT-A (work order WO-TWWUCT-A).  `non_mf_group_notes.tex` applies
Tikuisis--White--Winter to `C⋆_r(G)` for amenable `G`, which requires the UCT
(`thm:fixed-radical-membership`).  The Higson--Kasparov/Tu route to the UCT goes
through reduced crossed products `A ⋊_r G` (D. Williams, *Crossed Products of
C⋆-Algebras*, ch. 2 and 7; Brown--Ozawa, *C⋆-Algebras and Finite-Dimensional
Approximations*, §4.1).  This file supplies the vocabulary.

* `GCStarAlgebra G A`: a discrete group `G` acting on a non-unital C⋆-algebra `A`
  by `⋆`-automorphisms, `act : G →* (A ≃⋆ₐ[ℂ] A)`.
* `IsEquivariant G φ`: a `⋆`-homomorphism intertwining the actions.
* The trivial action of any group on `ℂ` (the only action by `ℂ`-linear
  `⋆`-automorphisms).
* `faithfulRep A`: a faithful representation of `A` on a
  Hilbert space, namely the direct sum of the GNS representations of all states
  of the unitization, restricted to `A`.  The reduced crossed product is built
  from it in `CrossedProductDef`; `CrossedProductNorm` shows that its norm does
  not depend on this choice.
-/

namespace GroupApproximation.Full.TWWUCT

open GroupApproximation.CStarState

universe u v w

noncomputable section

/-- **`G`-C⋆-algebra** (Williams, Def. 2.7): a discrete group `G` acting on a
non-unital C⋆-algebra by `⋆`-automorphisms.  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
class GCStarAlgebra (G : Type u) [Group G] (A : Type v) [NonUnitalCStarAlgebra A] where
  /-- The action by `⋆`-automorphisms. -/
  act : G →* (A ≃⋆ₐ[ℂ] A)

namespace GCStarAlgebra

variable {G : Type u} [Group G] {A : Type v} [NonUnitalCStarAlgebra A] [GCStarAlgebra G A]

theorem act_one_apply (a : A) : GCStarAlgebra.act (A := A) (1 : G) a = a := by
  rw [map_one, StarAlgEquiv.one_apply]

theorem act_mul_apply (g h : G) (a : A) :
    GCStarAlgebra.act (A := A) (g * h) a =
      GCStarAlgebra.act (A := A) g (GCStarAlgebra.act (A := A) h a) := by
  rw [map_mul, StarAlgEquiv.mul_apply]

theorem act_inv_act (g : G) (a : A) :
    GCStarAlgebra.act (A := A) g⁻¹ (GCStarAlgebra.act (A := A) g a) = a := by
  rw [← act_mul_apply, inv_mul_cancel, act_one_apply]

theorem act_act_inv (g : G) (a : A) :
    GCStarAlgebra.act (A := A) g (GCStarAlgebra.act (A := A) g⁻¹ a) = a := by
  rw [← act_mul_apply, mul_inv_cancel, act_one_apply]

theorem act_star (g : G) (a : A) :
    GCStarAlgebra.act (A := A) g (star a) = star (GCStarAlgebra.act (A := A) g a) :=
  map_star _ a

theorem act_mul (g : G) (a b : A) :
    GCStarAlgebra.act (A := A) g (a * b) =
      GCStarAlgebra.act (A := A) g a * GCStarAlgebra.act (A := A) g b :=
  map_mul _ a b

theorem norm_act (g : G) (a : A) : ‖GCStarAlgebra.act (A := A) g a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (GCStarAlgebra.act (A := A) g)
    (EquivLike.injective (GCStarAlgebra.act (A := A) g)) a

end GCStarAlgebra

/-- The trivial action of a group on `ℂ`.  Every `ℂ`-linear `⋆`-automorphism of `ℂ`
is the identity, so this is the only `G`-C⋆-algebra structure on `ℂ`.
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
instance instGCStarAlgebraComplex (G : Type u) [Group G] : GCStarAlgebra G ℂ where
  act := 1

theorem act_complex_apply {G : Type u} [Group G] (g : G) (z : ℂ) :
    GCStarAlgebra.act (A := ℂ) g z = z :=
  rfl

section Equivariant

variable (G : Type u) [Group G]
variable {A : Type v} {B : Type w} {C : Type*}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
variable [GCStarAlgebra G A] [GCStarAlgebra G B] [GCStarAlgebra G C]

/-- **Equivariant `⋆`-homomorphism** (Williams, §2.1): `φ (g · a) = g · φ a`.
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
def IsEquivariant (φ : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∀ (g : G) (a : A),
    φ (GCStarAlgebra.act (A := A) g a) = GCStarAlgebra.act (A := B) g (φ a)

theorem isEquivariant_id : IsEquivariant G (NonUnitalStarAlgHom.id ℂ A) :=
  fun _ _ => rfl

variable {G}

theorem IsEquivariant.comp {ψ : B →⋆ₙₐ[ℂ] C} {φ : A →⋆ₙₐ[ℂ] B}
    (hψ : IsEquivariant G ψ) (hφ : IsEquivariant G φ) : IsEquivariant G (ψ.comp φ) := by
  intro g a
  change ψ (φ (GCStarAlgebra.act (A := A) g a)) = GCStarAlgebra.act (A := C) g (ψ (φ a))
  rw [hφ g a, hψ g (φ a)]

end Equivariant

/-! ## A faithful representation -/

section Faithful

variable (A : Type v) [NonUnitalCStarAlgebra A]

/-- The Hilbert space of `faithfulRep A`: the Hilbert sum of the GNS spaces of all
states of the unitization of `A`. -/
abbrev FaithfulSpace : Type v :=
  FamilyGNSSpace (id : State (Unitization ℂ A) → State (Unitization ℂ A))

/-- **A faithful representation of a non-unital C⋆-algebra** (Gelfand--Naimark):
the universal GNS representation of the unitization, restricted to `A`.
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
def faithfulRep : A →⋆ₙₐ[ℂ] (FaithfulSpace A →L[ℂ] FaithfulSpace A) :=
  (familyGNSStarAlgHom
      (id : State (Unitization ℂ A) → State (Unitization ℂ A))).toNonUnitalStarAlgHom.comp
    (Unitization.inrNonUnitalStarAlgHom ℂ A)

theorem faithfulRep_apply (a : A) :
    faithfulRep A a =
      familyGNSStarAlgHom (id : State (Unitization ℂ A) → State (Unitization ℂ A))
        (a : Unitization ℂ A) :=
  rfl

theorem faithfulRep_injective : Function.Injective (faithfulRep A) := by
  have hsep : ∀ x : Unitization ℂ A, x ≠ 0 →
      ∃ φ : State (Unitization ℂ A), ((φ.gnsRep).hom x) ≠ 0 := by
    intro x hx
    obtain ⟨φ, hφ⟩ := exists_state_norm_le_gnsRep x
    refine ⟨φ, fun h => hx ?_⟩
    rw [h, norm_zero] at hφ
    exact norm_le_zero_iff.mp hφ
  intro a b hab
  have hab' :
      familyGNSStarAlgHom (id : State (Unitization ℂ A) → State (Unitization ℂ A))
          (a : Unitization ℂ A) =
        familyGNSStarAlgHom (id : State (Unitization ℂ A) → State (Unitization ℂ A))
          (b : Unitization ℂ A) := hab
  exact Unitization.inr_injective
    (familyGNSStarAlgHom_injective
      (id : State (Unitization ℂ A) → State (Unitization ℂ A)) hsep hab')

theorem norm_faithfulRep (a : A) : ‖faithfulRep A a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (faithfulRep A) (faithfulRep_injective A) a

end Faithful

end

end GroupApproximation.Full.TWWUCT
