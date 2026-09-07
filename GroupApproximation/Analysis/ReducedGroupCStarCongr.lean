import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.CStarSimple
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# `C*_r` is functorial in group isomorphisms

Isomorphic groups have ⋆-isomorphic reduced C⋆-algebras.  The repository had no
such transport: `IsSimpleCStar.of_starAlgEquiv` moves simplicity along a
⋆-isomorphism, but nothing produced the ⋆-isomorphism
`C*_r(G) ≃⋆ₐ[ℂ] C*_r(H)` from `G ≃* H`.

## Why it is needed

`Manuscript/NonMF/DGOTheorem235Slice.lean` states Powers' theorem at a group
that *is* free of rank at least two, which is how the theorem reads and how step
4 of Dahmani--Guirardel--Osin's proof of their Theorem 2.35 consumes it: there
the free group is a *normal subgroup* `F ≤ G` that happens to be free, not a copy
of `FreeGroup X`.  Anyone proving `PowersFreeGroupCStarSimple` therefore has to
carry a proof about `FreeGroup X` across an isomorphism, and this module is what
lets them.

Nothing here is specific to that lane — this is the general statement.

## The construction

`G ≃* H` is in particular a bijection of the index sets, so it induces a unitary
`ℓ²(G) ≃ₗᵢ[ℂ] ℓ²(H)` by permuting coordinates (`lpCongrLeft`), and conjugation
by a unitary is a ⋆-isomorphism of the ambient bounded-operator algebras
(Mathlib's `LinearIsometryEquiv.conjStarAlgEquiv`).  The whole content is then
one computation, `groupHilbertCongr_intertwines`:

  `U ∘ λ_G(g) = λ_H(φ g) ∘ U`,

after which conjugation carries `λ_G(g)` to `λ_H(φ g)`, hence the range of the
left regular representation onto the range of the other, hence the star
subalgebra they generate, hence — the conjugation being isometric — its closure.

The intertwining is stated and proved in the *forward* direction on both sides
deliberately: it needs only `lpCongrLeft_apply`, and never the value of
`(lpCongrLeft e).symm`, for which this repository has no lemma.  The
`e.symm` that `conjStarAlgEquiv` introduces is then discharged by
`LinearIsometryEquiv.apply_symm_apply` rather than computed.
-/

namespace GroupApproximation
namespace ReducedGroupCStarTrace

open scoped ComplexConjugate

universe u

variable {G H : Type u} [Group G] [Group H]

/-! ## The unitary induced by a group isomorphism -/

/-- **The unitary `ℓ²(G) ≃ ℓ²(H)` induced by a group isomorphism**, by permuting
coordinates.  Only the underlying bijection is used; the group structure enters
in `groupHilbertCongr_intertwines`. -/
noncomputable def groupHilbertCongr (φ : G ≃* H) :
    GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H :=
  lpCongrLeft φ.toEquiv

@[simp]
theorem groupHilbertCongr_apply (φ : G ≃* H) (f : GroupHilbert G) (x : H) :
    groupHilbertCongr φ f x = f (φ.symm x) :=
  rfl

/-- **The intertwining relation** `U ∘ λ_G(g) = λ_H(φ g) ∘ U`.

Both sides are evaluated forwards, so the proof uses only `lpCongrLeft_apply`;
the identity behind it is `φ.symm ((φ g)⁻¹ * x) = g⁻¹ * φ.symm x`, which is
multiplicativity of `φ.symm` together with `φ.symm (φ g) = g`. -/
theorem groupHilbertCongr_intertwines (φ : G ≃* H) (g : G) (f : GroupHilbert G) :
    groupHilbertCongr φ (leftRegularOperator G g f)
      = leftRegularOperator H (φ g) (groupHilbertCongr φ f) := by
  ext x
  have harg : φ.symm ((φ g)⁻¹ * x) = g⁻¹ * φ.symm x := by
    rw [map_mul, map_inv, MulEquiv.symm_apply_apply]
  simp only [groupHilbertCongr_apply, leftRegularOperator_apply, harg]

/-- **Conjugation carries the left regular representation of `G` onto that of
`H`.**  This is the whole content of the module; everything below is transport. -/
theorem conjStarAlgEquiv_leftRegularOperator (φ : G ≃* H) (g : G) :
    (groupHilbertCongr φ).conjStarAlgEquiv (leftRegularOperator G g)
      = leftRegularOperator H (φ g) := by
  ext y
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    groupHilbertCongr_intertwines, LinearIsometryEquiv.apply_symm_apply]

/-- The conjugation ⋆-isomorphism sends the range of `λ_G` onto the range of
`λ_H`.  Surjectivity of `φ` is what makes it onto. -/
theorem image_range_leftRegularOperator (φ : G ≃* H) :
    (groupHilbertCongr φ).conjStarAlgEquiv.toStarAlgHom ''
        (Set.range (leftRegularOperator G))
      = Set.range (leftRegularOperator H) := by
  ext T
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨φ g, (conjStarAlgEquiv_leftRegularOperator φ g).symm⟩
  · rintro ⟨h, rfl⟩
    refine ⟨leftRegularOperator G (φ.symm h), ⟨φ.symm h, rfl⟩, ?_⟩
    show (groupHilbertCongr φ).conjStarAlgEquiv (leftRegularOperator G (φ.symm h))
      = leftRegularOperator H h
    rw [conjStarAlgEquiv_leftRegularOperator, MulEquiv.apply_symm_apply]

/-! ## Transport of the reduced C⋆-algebra -/

/-- The conjugation ⋆-isomorphism and its inverse are isometric, hence it is
continuous and a closed map — the two facts
`StarSubalgebra.topologicalClosure_map` asks for. -/
theorem isometry_conjStarAlgEquiv (φ : G ≃* H) :
    Isometry ((groupHilbertCongr φ).conjStarAlgEquiv) :=
  StarAlgEquiv.isometry _

/-- **The reduced group C⋆-algebra transports.**  The image of
`reducedGroupCStarSubalgebra G` under conjugation is
`reducedGroupCStarSubalgebra H`, as star subalgebras of `B(ℓ²H)`. -/
theorem map_reducedGroupCStarSubalgebra (φ : G ≃* H) :
    (reducedGroupCStarSubalgebra G).map
        (groupHilbertCongr φ).conjStarAlgEquiv.toStarAlgHom
      = reducedGroupCStarSubalgebra H := by
  have hcont : Continuous ((groupHilbertCongr φ).conjStarAlgEquiv) :=
    (isometry_conjStarAlgEquiv φ).continuous
  have hcontsymm : Continuous ((groupHilbertCongr φ).conjStarAlgEquiv.symm) :=
    (StarAlgEquiv.isometry _).continuous
  have hclosed : IsClosedMap ((groupHilbertCongr φ).conjStarAlgEquiv) :=
    (Homeomorph.mk (groupHilbertCongr φ).conjStarAlgEquiv.toRingEquiv.toEquiv
      hcont hcontsymm).isClosedMap
  show (StarAlgebra.adjoin ℂ (Set.range (leftRegularOperator G))).topologicalClosure.map
      (groupHilbertCongr φ).conjStarAlgEquiv.toStarAlgHom
    = (StarAlgebra.adjoin ℂ (Set.range (leftRegularOperator H))).topologicalClosure
  rw [← StarSubalgebra.topologicalClosure_map _ _ hclosed hcont,
    StarAlgHom.map_adjoin, image_range_leftRegularOperator]

/-- Conjugation lands an element of `C*_r(G)` in `C*_r(H)`. -/
theorem mem_reducedGroupCStarSubalgebra_conj (φ : G ≃* H)
    (x : ReducedGroupCStar G) :
    (groupHilbertCongr φ).conjStarAlgEquiv (x : _) ∈ reducedGroupCStarSubalgebra H := by
  rw [← map_reducedGroupCStarSubalgebra φ]
  exact ⟨(x : _), x.2, rfl⟩

/-- The restriction of the ambient conjugation to a ⋆-homomorphism between the
two reduced algebras.  Built by `codRestrict` from the inclusion, so no
homomorphism field has to be re-verified. -/
noncomputable def reducedGroupCStarCongrHom (φ : G ≃* H) :
    ReducedGroupCStar G →⋆ₐ[ℂ] ReducedGroupCStar H :=
  StarAlgHom.codRestrict
    (((groupHilbertCongr φ).conjStarAlgEquiv.toStarAlgHom).comp
      (reducedGroupCStarSubalgebra G).subtype)
    (reducedGroupCStarSubalgebra H)
    (mem_reducedGroupCStarSubalgebra_conj φ)

@[simp]
theorem reducedGroupCStarCongrHom_coe (φ : G ≃* H) (x : ReducedGroupCStar G) :
    (reducedGroupCStarCongrHom φ x : GroupHilbert H →L[ℂ] GroupHilbert H)
      = (groupHilbertCongr φ).conjStarAlgEquiv (x : _) :=
  rfl

/-- **`C*_r(G) ≃⋆ₐ[ℂ] C*_r(H)` from `G ≃* H`.**

The restriction of the ambient conjugation to the two reduced algebras.  It is
bijective because `map_reducedGroupCStarSubalgebra` identifies the image with
the target exactly. -/
noncomputable def reducedGroupCStarCongr (φ : G ≃* H) :
    ReducedGroupCStar G ≃⋆ₐ[ℂ] ReducedGroupCStar H := by
  refine StarAlgEquiv.ofBijective (reducedGroupCStarCongrHom φ) ⟨?_, ?_⟩
  · intro x y hxy
    have h := congrArg (fun z : ReducedGroupCStar H =>
      (z : GroupHilbert H →L[ℂ] GroupHilbert H)) hxy
    simp only [reducedGroupCStarCongrHom_coe] at h
    exact Subtype.ext ((groupHilbertCongr φ).conjStarAlgEquiv.injective h)
  · intro y
    have hy : (y : GroupHilbert H →L[ℂ] GroupHilbert H) ∈
        (reducedGroupCStarSubalgebra G).map
          (groupHilbertCongr φ).conjStarAlgEquiv.toStarAlgHom := by
      rw [map_reducedGroupCStarSubalgebra φ]; exact y.2
    obtain ⟨a, ha, hae⟩ := hy
    exact ⟨⟨a, ha⟩, Subtype.ext hae⟩

/-- **Simplicity of the reduced C⋆-algebra is an isomorphism invariant of the
group.**  The corollary the slice needs: a proof of Powers' theorem for
`FreeGroup X` reaches every group that is free of that rank. -/
theorem isSimpleCStar_reducedGroupCStar_congr (φ : G ≃* H)
    (h : IsSimpleCStar (ReducedGroupCStar G)) :
    IsSimpleCStar (ReducedGroupCStar H) :=
  IsSimpleCStar.of_starAlgEquiv (reducedGroupCStarCongr φ) h

end ReducedGroupCStarTrace
end GroupApproximation

open GroupApproximation.ReducedGroupCStarTrace

#audit_axioms conjStarAlgEquiv_leftRegularOperator
#audit_axioms map_reducedGroupCStarSubalgebra
#audit_axioms reducedGroupCStarCongr
#audit_axioms isSimpleCStar_reducedGroupCStar_congr
