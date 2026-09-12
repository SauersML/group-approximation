import GroupApproximation.Analysis.LocallyRFByIntFactorization
import GroupApproximation.Sofic.LEFMarkedCompression

/-!
# The affine--Clifford witness is locally residually finite by the integers

The explicit non-MF witness is constructed as

`CliffordLamp X ⋊ (Telescope ⋊ ℤ)`.

Re-associating it exposes the shift kernel `CliffordLamp X ⋊ Telescope`.
The finite invariant windows already used to prove that kernel LEF actually
prove the stronger fact needed for the factorization-property construction:
every finitely generated subgroup of the kernel is residually finite.

Everything here is internal to the affine--Clifford model.  In particular,
there is no factorization-property or trace-amenability assumption.
-/

namespace GroupApproximation

open SemidirectProduct
open LocallyRFByIntAmenableTrace

noncomputable section

variable {N G : Type} [Group N] [Group G]

/-- Finite invariant residual windows imply local residual finiteness of a
semidirect product.  This is the stronger local conclusion hidden inside the
standard finite-window proof of LEF. -/
theorem isLocallyResiduallyFinite_semidirectProduct_of_invariant_finite
    (phi : G →* MulAut N)
    (hlocal : ∀ F : Finset (N ⋊[phi] G), ∃ (K : Subgroup N) (H : Subgroup G),
      Finite K ∧ Group.ResiduallyFinite H ∧
        (∀ h ∈ H, ∀ n ∈ K, phi h n ∈ K) ∧
        (∀ g ∈ F, g.left ∈ K ∧ g.right ∈ H)) :
    IsLocallyResiduallyFinite (N ⋊[phi] G) := by
  classical
  intro Q hQ
  obtain ⟨S, hSQ, hSfin⟩ := (Subgroup.fg_iff Q).mp hQ
  obtain ⟨K, H, hKfin, hHrf, hinv, hmem⟩ := hlocal hSfin.toFinset
  haveI : Finite K := hKfin
  haveI : Group.ResiduallyFinite H := hHrf
  let T : Subgroup (N ⋊[phi] G) := (inclSemidirect phi K H hinv).range
  have hTrf : Group.ResiduallyFinite T := by
    haveI : Finite (MulAut K) :=
      Finite.of_injective (fun e : MulAut K ↦ (e : K → K)) DFunLike.coe_injective
    haveI : Group.ResiduallyFinite (K ⋊[restrictAut phi K H hinv] H) :=
      residuallyFinite_semidirectProduct_of_finite_range _
    exact residuallyFinite_of_mulEquiv
      (MonoidHom.ofInjective (inclSemidirect_injective phi K H hinv)).symm
  have hQT : Q ≤ T := by
    rw [← hSQ]
    refine (Subgroup.closure_le T).mpr ?_
    intro g hg
    obtain ⟨hgK, hgH⟩ := hmem g (hSfin.mem_toFinset.mpr hg)
    exact ⟨⟨⟨g.left, hgK⟩, ⟨g.right, hgH⟩⟩, by
      rw [inclSemidirect_apply]⟩
  letI : Group.ResiduallyFinite T := hTrf
  exact residuallyFinite_of_injective (Subgroup.inclusion hQT)
    (Subgroup.inclusion_injective hQT)

namespace CliffordWitnessLocallyRFByInt

open CliffordLamp MappingTelescope MarkedCompression
open SoficMarkedCompression

/-- For any injective finite-index self-embedding, the kernel exposed by
moving the integer shift to the outside of its Clifford witness. -/
abbrev ShiftKernelFor {Γ : Type} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) : Type :=
  CliffordLamp (Cosets α hα) ⋊[
    SemidirectAssoc.baseAction (shiftHom α hα) (lampAction α hα)]
    Telescope α hα

/-- The integer shift action on the general lamp--telescope kernel. -/
abbrev shiftActionFor {Γ : Type} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) :
    Multiplicative ℤ →* MulAut (ShiftKernelFor α hα) :=
  SemidirectAssoc.outerAction (shiftHom α hα) (lampAction α hα)

/-- Every finitely generated subgroup of the shift kernel associated to a
residually finite group and a finite-index injective self-embedding is
residually finite. -/
theorem shiftKernelFor_isLocallyResiduallyFinite
    {Γ : Type} [Group Γ] [Group.ResiduallyFinite Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) [α.range.FiniteIndex] :
    IsLocallyResiduallyFinite (ShiftKernelFor α hα) := by
  classical
  apply isLocallyResiduallyFinite_semidirectProduct_of_invariant_finite
  intro F
  choose lvl elt hrepr using fun g : ShiftKernelFor α hα ↦
    exists_level_repr α hα g.right
  let levelNumber : ℕ := F.sup lvl
  let H : Subgroup (Telescope α hα) :=
    (level α hα levelNumber).range
  let rho : H →* Equiv.Perm (Cosets α hα) :=
    levelSiteAction α hα levelNumber
  obtain ⟨K, hKfinite, hKinvariant, hKcontains⟩ :=
    CliffordLamp.exists_finite_invariant_clifford_subgroup rho
      (finite_levelSiteAction_orbit α hα levelNumber)
      (F.image SemidirectProduct.left)
  refine ⟨K, H, hKfinite, ?_, ?_, ?_⟩
  · exact residuallyFinite_of_mulEquiv
      (MonoidHom.ofInjective
        (level_injective α hα levelNumber)).symm
  · intro h hh n hn
    exact hKinvariant (⟨h, hh⟩ : H) n hn
  · intro g hg
    constructor
    · exact hKcontains g.left (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    · have hle : lvl g ≤ levelNumber := Finset.le_sup (f := lvl) hg
      have hmem := level_mem_range_of_le α hα hle (elt g)
      rwa [hrepr g] at hmem

def PrintedShiftKernelForIsLocallyResiduallyFinite : Prop :=
  ∀ (Γ : Type) [Group Γ] [Group.ResiduallyFinite Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) [α.range.FiniteIndex],
    IsLocallyResiduallyFinite (ShiftKernelFor α hα)

theorem manuscriptShiftKernelForIsLocallyResiduallyFinite :
    PrintedShiftKernelForIsLocallyResiduallyFinite := by
  intro Γ _ _ α hα _
  exact shiftKernelFor_isLocallyResiduallyFinite α hα

/-- The general Clifford witness re-associated as its shift kernel extended
by the integers. -/
def ambientEquivShiftKernelForByInt {Γ : Type} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) :
    Ambient α hα ≃* (ShiftKernelFor α hα ⋊[shiftActionFor α hα]
      Multiplicative ℤ) :=
  (SemidirectAssoc.assocEquiv (shiftHom α hα) (lampAction α hα)).symm

def PrintedAmbientEquivShiftKernelForByInt : Prop :=
  ∀ (Γ : Type) [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α),
    Nonempty (Ambient α hα ≃*
      (ShiftKernelFor α hα ⋊[shiftActionFor α hα] Multiplicative ℤ))

theorem manuscriptAmbientEquivShiftKernelForByInt :
    PrintedAmbientEquivShiftKernelForByInt := by
  intro Γ _ α hα
  exact ⟨ambientEquivShiftKernelForByInt α hα⟩

open ExplicitLinearModel LiteralNonMFLinearWitness

/-- The kernel exposed by the concrete integral affine self-embedding. -/
abbrev ShiftKernel : Type := ShiftKernelFor alpha conjD_injective

/-- The concrete integer shift action. -/
abbrev shiftAction : Multiplicative ℤ →* MulAut ShiftKernel :=
  shiftActionFor alpha conjD_injective

/-- The general theorem specialized to the integral affine base. -/
theorem shiftKernel_isLocallyResiduallyFinite :
    IsLocallyResiduallyFinite ShiftKernel := by
  letI : Group.ResiduallyFinite gammaBar :=
    ExplicitIntegralLinearModel.gammaBar_residuallyFinite
  exact shiftKernelFor_isLocallyResiduallyFinite alpha conjD_injective

/-- The explicit affine--Clifford witness, re-associated as its locally
residually finite shift kernel extended by the integers. -/
def witnessGroupEquivShiftKernelByInt :
    WitnessGroup ≃* (ShiftKernel ⋊[shiftAction] Multiplicative ℤ) :=
  ambientEquivShiftKernelForByInt alpha conjD_injective

/-- The canonical maximal trace of the explicit affine--Clifford witness is
amenable, by its locally-residually-finite-by-integer decomposition. -/
theorem witnessCanonicalMaximalTrace_isAmenableTrace :
    Quasidiagonal.IsAmenableTrace
      (fun a : MaximalGroupCStar WitnessGroup ↦
        canonicalMaximalTrace WitnessGroup a) :=
  LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt
    shiftAction witnessGroupEquivShiftKernelByInt
      shiftKernel_isLocallyResiduallyFinite

end CliffordWitnessLocallyRFByInt

end
end GroupApproximation

open GroupApproximation
open GroupApproximation.CliffordWitnessLocallyRFByInt

#audit_axioms isLocallyResiduallyFinite_semidirectProduct_of_invariant_finite
#audit_axioms shiftKernelFor_isLocallyResiduallyFinite
#audit_axioms ambientEquivShiftKernelForByInt
#audit_closed_axioms shiftKernel_isLocallyResiduallyFinite
#audit_closed_axioms witnessGroupEquivShiftKernelByInt
#audit_closed_axioms witnessCanonicalMaximalTrace_isAmenableTrace
