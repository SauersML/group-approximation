import GroupApproximation.Algebra.SemidirectProductAssoc
import GroupApproximation.Sofic.FiniteOrbitInvariantKernel
import GroupApproximation.Sofic.MappingTelescopeFiniteOrbits
import GroupApproximation.Sofic.SoficIntegerExtension

/-!
# Soficity of the marked-compression witness

Assume that the base group is sofic and that the compressing endomorphism
has finite-index range.  Every finite window in the telescope lies in one
level.  That level has finite orbits on the coset space of the base, so a
finite Clifford-lamp window lies in a finite level-invariant subgroup.
The lamp-by-telescope group is therefore sofic by the local finite-kernel
criterion.  Reassociating the remaining semidirect product and adjoining the
integer shift then proves that the full marked-compression group is sofic.
-/

namespace GroupApproximation
namespace SoficMarkedCompression

open CliffordLamp MappingTelescope MarkedCompression SemidirectProduct

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The action of a telescope level on the marked coset space. -/
def levelSiteAction (n : ℕ) :
    (level α hα n).range →* Equiv.Perm (Cosets α hα) :=
  (MulAction.toPermHom (Vertical α hα) (Cosets α hα)).comp
    ((inl : Telescope α hα →* Vertical α hα).comp
      (level α hα n).range.subtype)

/-- Finite index of the compression makes every telescope-level site orbit
finite. -/
theorem finite_levelSiteAction_orbit [α.range.FiniteIndex] (n : ℕ)
    (x : Cosets α hα) :
    (Set.range fun h : (level α hα n).range ↦
      levelSiteAction α hα n h x).Finite := by
  refine (MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit
    α hα n x).subset ?_
  rintro _ ⟨h, rfl⟩
  obtain ⟨γ, hγ⟩ := h.2
  refine ⟨⟨inl (h : Telescope α hα), ?_⟩, rfl⟩
  exact ⟨γ, congrArg inl hγ⟩

/-- The level action on Clifford lamps is the restriction of the inner
action obtained by reassociating the witness tower. -/
@[simp] theorem level_action_eq_baseAction (n : ℕ)
    (h : (level α hα n).range) :
    CliffordLamp.actionHom (levelSiteAction α hα n) h =
      SemidirectAssoc.baseAction (shiftHom α hα) (lampAction α hα) h :=
  rfl

/-- The Clifford-lamp-by-telescope subgroup is sofic. -/
theorem isSofic_lamp_telescope [α.range.FiniteIndex] (hΓ : IsSofic Γ) :
    IsSofic
      (CliffordLamp (Cosets α hα) ⋊[
        SemidirectAssoc.baseAction (shiftHom α hα) (lampAction α hα)]
        Telescope α hα) := by
  classical
  apply isSofic_semidirectProduct_of_invariant_finite
  intro F
  choose lvl elt hrepr using fun g :
    CliffordLamp (Cosets α hα) ⋊[
      SemidirectAssoc.baseAction (shiftHom α hα) (lampAction α hα)]
      Telescope α hα ↦ exists_level_repr α hα g.right
  let N : ℕ := F.sup lvl
  let H : Subgroup (Telescope α hα) := (level α hα N).range
  let ρ : H →* Equiv.Perm (Cosets α hα) := levelSiteAction α hα N
  obtain ⟨K, hKfinite, hKinvariant, hKcontains⟩ :=
    CliffordLamp.exists_finite_invariant_clifford_subgroup ρ
      (finite_levelSiteAction_orbit α hα N)
      (F.image SemidirectProduct.left)
  refine ⟨K, H, hKfinite, isSofic_level_range α hα hΓ N, ?_, ?_⟩
  · intro h hh n hn
    -- the two actions are definitionally equal, as `level_action_eq_baseAction`
    -- records; `rw` cannot see through the `MulAut` coercion, so close by defeq
    exact hKinvariant (⟨h, hh⟩ : H) n hn
  · intro g hg
    constructor
    · exact hKcontains g.left (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    · have hle : lvl g ≤ N := Finset.le_sup (f := lvl) hg
      have hmem := level_mem_range_of_le α hα hle (elt g)
      rwa [hrepr g] at hmem

/-- **Soficity of the full marked-compression construction.** -/
theorem isSofic_ambient [α.range.FiniteIndex] (hΓ : IsSofic Γ) :
    IsSofic (Ambient α hα) := by
  have hinner := isSofic_lamp_telescope α hα hΓ
  have houter : IsSofic
      ((CliffordLamp (Cosets α hα) ⋊[
          SemidirectAssoc.baseAction (shiftHom α hα) (lampAction α hα)]
          Telescope α hα) ⋊[
        SemidirectAssoc.outerAction (shiftHom α hα) (lampAction α hα)]
        Multiplicative ℤ) :=
    SoficIntegerExtension.isSofic_int_semidirectProduct
      (SemidirectAssoc.outerAction (shiftHom α hα) (lampAction α hα)) hinner
  exact (isSofic_mulEquiv_iff
    (SemidirectAssoc.assocEquiv (shiftHom α hα) (lampAction α hα))).mp houter

end SoficMarkedCompression
end GroupApproximation
