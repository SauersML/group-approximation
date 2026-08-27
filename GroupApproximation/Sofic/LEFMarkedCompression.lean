import GroupApproximation.Sofic.SoficMarkedCompression
import GroupApproximation.Sofic.SoficInvariantFiniteKernel
import GroupApproximation.Sofic.SoficTelescope
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.LiteralWitnessConsequences

/-!
# The witness is an extension of an LEF group by the integers

The witness tower `Ambient = Lamp ⋊ (Telescope ⋊ ℤ)` projects onto its
integer shift.  The kernel of that projection is the lamp-by-telescope
group.  Every finite window of it sits inside a finite invariant lamp
subgroup together with one telescope level, and a telescope level is a
copy of the residually finite base.  A finite-kernel semidirect product
with residually finite quotient is residually finite because the action
has finite range, so the kernel is exhausted by residually finite
subgroups and is therefore LEF.

The endpoint sharpens the extension non-permanence of operator MF: the
witness is an extension of an LEF group by `ℤ` with non-MF total group,
while soficity is preserved by all such extensions.
-/

namespace GroupApproximation

variable {N : Type} {G : Type*} [Group N] [Group G]

/-- **LEF for a locally finite invariant kernel over a locally residually
finite base.**  If every finite window of `N ⋊ G` can be enclosed in a
finite `G`-invariant subgroup of `N` together with a residually finite
subgroup of `G` acting on it, then `N ⋊ G` is LEF: the enclosing pair
spans a finite-kernel semidirect product with finite-range action, which
is residually finite, and LEF is local over such subgroups. -/
theorem isLEF_semidirectProduct_of_invariant_finite
    (φ : G →* MulAut N)
    (hlocal : ∀ F : Finset (N ⋊[φ] G), ∃ (K : Subgroup N) (H : Subgroup G),
      Finite K ∧ Group.ResiduallyFinite H ∧ (∀ h ∈ H, ∀ n ∈ K, φ h n ∈ K) ∧
        (∀ g ∈ F, g.left ∈ K ∧ g.right ∈ H)) :
    IsLEF (N ⋊[φ] G) := by
  classical
  apply isLEF_of_forall_finset_residuallyFinite
  intro F
  obtain ⟨K, H, hKfin, hHrf, hinv, hmem⟩ := hlocal F
  haveI : Finite K := hKfin
  haveI : Group.ResiduallyFinite H := hHrf
  refine ⟨(inclSemidirect φ K H hinv).range, ?_, ?_⟩
  · intro g hg
    obtain ⟨hleft, hright⟩ := hmem g hg
    refine ⟨⟨⟨g.left, hleft⟩, ⟨g.right, hright⟩⟩, ?_⟩
    rw [inclSemidirect_apply]
  · haveI : Finite (MulAut K) :=
      Finite.of_injective (fun e : MulAut K ↦ (e : K → K))
        DFunLike.coe_injective
    haveI : Group.ResiduallyFinite (K ⋊[restrictAut φ K H hinv] H) :=
      residuallyFinite_semidirectProduct_of_finite_range _
    exact residuallyFinite_of_mulEquiv
      (MonoidHom.ofInjective (inclSemidirect_injective φ K H hinv)).symm

namespace LEFMarkedCompression

open CliffordLamp MappingTelescope MarkedCompression SemidirectProduct
open SoficMarkedCompression

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The Clifford-lamp-by-telescope subgroup is LEF when the compression has
finite-index range and the base is residually finite. -/
theorem isLEF_lamp_telescope [α.range.FiniteIndex]
    [Group.ResiduallyFinite Γ] :
    IsLEF
      (CliffordLamp (Cosets α hα) ⋊[
        SemidirectAssoc.baseAction (shiftHom α hα) (lampAction α hα)]
        Telescope α hα) := by
  classical
  apply isLEF_semidirectProduct_of_invariant_finite
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
  refine ⟨K, H, hKfinite, ?_, ?_, ?_⟩
  · exact residuallyFinite_of_mulEquiv
      (MonoidHom.ofInjective (level_injective α hα N)).symm
  · intro h hh n hn
    -- the two actions are definitionally equal, as `level_action_eq_baseAction`
    -- records; close by defeq exactly as in the soficity proof
    exact hKinvariant (⟨h, hh⟩ : H) n hn
  · intro g hg
    constructor
    · exact hKcontains g.left (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    · have hle : lvl g ≤ N := Finset.le_sup (f := lvl) hg
      have hmem := level_mem_range_of_le α hα hle (elt g)
      rwa [hrepr g] at hmem

end LEFMarkedCompression

namespace LiteralLEFExtension

open CliffordLamp MappingTelescope MarkedCompression SemidirectProduct
open ExplicitLinearModel LiteralNonMFLinearWitness LiteralWitnessConsequences

noncomputable section

local instance : Countable (Multiplicative ℤ) :=
  Countable.of_equiv ℤ Multiplicative.toAdd

/-- The projection of the explicit witness onto its integer shift. -/
def zShiftProjection : WitnessGroup →* Multiplicative ℤ :=
  (SemidirectProduct.rightHom :
      Vertical alpha conjD_injective →* Multiplicative ℤ).comp
    (SemidirectProduct.rightHom :
      WitnessGroup →* Vertical alpha conjD_injective)

theorem zShiftProjection_surjective :
    Function.Surjective zShiftProjection := by
  intro z
  exact ⟨SemidirectProduct.inr (SemidirectProduct.inr z), rfl⟩

/-- The kernel of the shift projection maps into the lamp-by-telescope
group by reading off its two inner coordinates. -/
def kerToLampTelescope :
    zShiftProjection.ker →*
      (CliffordLamp (Cosets alpha conjD_injective) ⋊[
        SemidirectAssoc.baseAction (shiftHom alpha conjD_injective)
          (lampAction alpha conjD_injective)]
        Telescope alpha conjD_injective) where
  toFun x := ⟨(x : WitnessGroup).left, (x : WitnessGroup).right.left⟩
  map_one' := rfl
  map_mul' x y := by
    have hx : ((x : WitnessGroup).right).right = 1 :=
      MonoidHom.mem_ker.mp x.2
    have hxinl : (x : WitnessGroup).right =
        SemidirectProduct.inl ((x : WitnessGroup).right.left) := by
      apply SemidirectProduct.ext
      · rfl
      · rw [hx, SemidirectProduct.right_inl]
    apply SemidirectProduct.ext
    · show ((x : WitnessGroup) * (y : WitnessGroup)).left =
        (x : WitnessGroup).left *
          SemidirectAssoc.baseAction (shiftHom alpha conjD_injective)
            (lampAction alpha conjD_injective)
            ((x : WitnessGroup).right.left) ((y : WitnessGroup).left)
      rw [SemidirectProduct.mul_left]
      congr 1
      rw [hxinl]
      rfl
    · show ((x : WitnessGroup) * (y : WitnessGroup)).right.left =
        (x : WitnessGroup).right.left * (y : WitnessGroup).right.left
      rw [SemidirectProduct.mul_right, SemidirectProduct.mul_left, hx]
      simp

theorem kerToLampTelescope_injective :
    Function.Injective kerToLampTelescope := by
  intro x y hxy
  have h1 : (x : WitnessGroup).left = (y : WitnessGroup).left := by
    have h0 := congrArg SemidirectProduct.left hxy
    exact h0
  have h2 : (x : WitnessGroup).right.left =
      (y : WitnessGroup).right.left := by
    have h0 := congrArg SemidirectProduct.right hxy
    exact h0
  have hx : ((x : WitnessGroup).right).right = 1 :=
    MonoidHom.mem_ker.mp x.2
  have hy : ((y : WitnessGroup).right).right = 1 :=
    MonoidHom.mem_ker.mp y.2
  apply Subtype.ext
  apply SemidirectProduct.ext h1
  apply SemidirectProduct.ext h2
  rw [hx, hy]

/-- The kernel of the shift projection is LEF. -/
theorem ker_zShiftProjection_isLEF : IsLEF zShiftProjection.ker := by
  haveI : Group.ResiduallyFinite gammaBar :=
    ExplicitIntegralLinearModel.gammaBar_residuallyFinite
  exact isLEF_of_injective kerToLampTelescope kerToLampTelescope_injective
    (LEFMarkedCompression.isLEF_lamp_telescope alpha conjD_injective)

/-- The kernel of the shift projection is operator MF. -/
theorem ker_zShiftProjection_isOperatorMF :
    IsOperatorMF zShiftProjection.ker :=
  isOperatorMF_of_isLEF ker_zShiftProjection_isLEF
/-- The integer quotient is operator MF. -/
theorem integerQuotient_isOperatorMF : IsOperatorMF (Multiplicative ℤ) :=
  isOperatorMF_of_isLEF isLEF_multiplicative_int

/-- **The witness is LEF-by-ℤ and not MF.**  The explicit sofic non-MF
witness fits into an extension whose kernel is LEF --- hence MF --- and
whose quotient is the integers: operator MF fails even for extensions
of LEF groups by the amenable group `ℤ`, whereas soficity is preserved
by every such extension. -/
theorem literalWitness_LEFKernel_integerExtension_nonMF :
    Function.Surjective zShiftProjection ∧
      IsLEF zShiftProjection.ker ∧
      IsOperatorMF zShiftProjection.ker ∧
      IsOperatorMF (Multiplicative ℤ) ∧
      Group.FG WitnessGroup ∧
      ¬ IsOperatorMF WitnessGroup :=
  ⟨zShiftProjection_surjective,
    ker_zShiftProjection_isLEF,
    ker_zShiftProjection_isOperatorMF,
    integerQuotient_isOperatorMF,
    witnessGroup_finitelyGenerated,
    witnessGroup_not_isOperatorMF⟩

end

end LiteralLEFExtension
end GroupApproximation
