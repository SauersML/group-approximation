import GroupApproximation.Sofic.LiteralDoublingWreathNonMF
import GroupApproximation.Sofic.ProfiniteTwins
import GroupApproximation.Algebra.PermutationalWreathRadicalTame

/-!
# The `A₅`-lamp group over the concrete doubling base

**Sections 43 and 52** of the ascending-HNN dossier, instantiated.
`Sofic/LiteralDoublingWreathNonMF` runs the endpoint with mod-two lamps; the
same concrete affine base carries any finite lamp group, and the interesting
choice is a nonabelian *simple* one.  With `K = A₅`:

* the lamp group is perfect, so nothing of it survives in an abelian quotient
  and the whole lamp base is the candidate radical;
* it is simple, so the kernel of the split projection is the normal closure of
  a **single** witness lamp -- one relation separates the wreath product from
  its skeleton;
* it is finite, so the kernel is locally finite, amenable, residually finite
  and MF: the failure of MF at the middle has nothing to do with a wild kernel;
* it contains an involution, which is what the unconditional collapse endpoint
  needs, so the group is **not MF** with no hypothesis at all.

`alternatingPackage` collects those clauses, and `alternatingTwins` adds the
profinite-twin statement for the first-stage quotient.  The double transposition
`(0 1)(2 3)` supplies the involution; everything else is transported from the
abstract endpoint.
-/

namespace GroupApproximation
namespace AlternatingLampLiteral

open SemidirectProduct MarkedCompression ExplicitLinearModel LiteralDoublingWreath

/-! ## An involution in `A₅` -/

/-- The double transposition `(0 1)(2 3)`. -/
def c5 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

theorem sign_c5 : Equiv.Perm.sign c5 = 1 := by
  rw [c5, map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

/-- The involution in `A₅` used as the lamp value. -/
def a5 : alternatingGroup (Fin 5) :=
  ⟨c5, Equiv.Perm.mem_alternatingGroup.mpr sign_c5⟩

theorem a5_ne_one : a5 ≠ 1 := by
  intro h
  have : c5 = 1 := congrArg Subtype.val h
  exact absurd this (by decide)

theorem a5_mul_self : a5 * a5 = 1 := by
  refine Subtype.ext ?_
  show c5 * c5 = 1
  decide

instance : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup (by simp)

/-! ## The group -/

/-- The `A₅`-lamp group over the coset space of the concrete doubling
extension. -/
abbrev WA : Type := WreathV (K := alternatingGroup (Fin 5)) conjD conjD_injective

instance : Countable WA := inferInstance

/-- The split quotient in the paper's headline theorem. -/
abbrev qA : WA →* Vertical conjD conjD_injective := SemidirectProduct.rightHom

/-- The canonical section of the headline quotient. -/
abbrev sectionA : Vertical conjD conjD_injective →* WA := SemidirectProduct.inr

/-- The single invisible relation: the double transposition at the witness
site. -/
noncomputable def rA : WA := witnessLamp conjD conjD_injective a5

theorem rA_ne_one : rA ≠ 1 := by
  intro h
  have hlamp : Lamp.single (tSite conjD conjD_injective) a5 = 1 :=
    inl_injective (by simpa [rA, witnessLamp] using h)
  have hvalue := congrArg
    (fun f : Lamp (alternatingGroup (Fin 5)) (Cosets conjD conjD_injective) =>
      f.toFun (tSite conjD conjD_injective)) hlamp
  exact a5_ne_one (by simpa using hvalue)

theorem rA_mul_self : rA * rA = 1 := by
  simpa [rA, pow_two] using
    witnessLamp_pow conjD conjD_injective a5 2 (by simpa [pow_two] using a5_mul_self)

theorem qA_comp_sectionA : qA.comp sectionA = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro g
  change (SemidirectProduct.rightHom :
      WA →* Vertical conjD conjD_injective) (SemidirectProduct.inr g) = g
  exact SemidirectProduct.rightHom_inr g

/-! ## The package -/

/-- **One relation is exactly the lamp kernel.**  The forward inclusion is
simplicity and transitivity of the coset action.  The reverse inclusion is
formal: the witness lamp belongs to the kernel of the wreath projection, and
that kernel is normal. -/
theorem ker_rightHom_eq_normalClosure_witnessLamp :
    (SemidirectProduct.rightHom : WA →* Vertical conjD conjD_injective).ker
      = Subgroup.normalClosure {witnessLamp conjD conjD_injective a5} := by
  apply le_antisymm
  · exact ker_le_normalClosure_witnessLamp conjD conjD_injective a5_ne_one
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    change (SemidirectProduct.rightHom :
      WA →* Vertical conjD conjD_injective)
        (witnessLamp conjD conjD_injective a5) = 1
    rfl

/-- **The `A₅` endpoint.**  The concrete group is not MF, unconditionally. -/
theorem not_isCDEOperatorMF_WA : ¬ IsCDEOperatorMF WA :=
  not_isCDEOperatorMF_wreath conjD conjD_injective
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT a5_ne_one a5_mul_self
    v1G_not_mem_range

theorem not_isOperatorMF_WA : ¬ IsOperatorMF WA := by
  intro h
  exact not_isCDEOperatorMF_WA ((isCDEOperatorMF_iff_isOperatorMF _).mpr h)

/-- **Sections 43, 51, 52, 54.2 at `A₅`.**  The kernel of the split projection
is the normal closure of one witness lamp, every subgroup of it is tame, and
the middle group is still not MF. -/
theorem alternatingPackage :
    (SemidirectProduct.rightHom : WA →* Vertical conjD conjD_injective).ker
        ≤ Subgroup.normalClosure {witnessLamp conjD conjD_injective a5} ∧
      (∀ H : Subgroup (Lamp (alternatingGroup (Fin 5))
          (Cosets conjD conjD_injective)),
        IsLocallyFiniteGroup H ∧ Amenability.IsAmenable H ∧
          IsResiduallyFinite H ∧ IsOperatorMF H) ∧
      ¬ IsOperatorMF WA :=
  ⟨ker_le_normalClosure_witnessLamp conjD conjD_injective a5_ne_one,
    fun H => lampSub_tame H, not_isOperatorMF_WA⟩

/-- **The `A₅` profinite twins.**  The group and its first-stage quotient have
the same finite quotients and opposite MF status, separated by a nontrivial
normal subgroup. -/
theorem alternatingTwins
    (hMF : IsOperatorMF (WA ⧸ stageRadical conjD conjD_injective a5)) :
    (∀ (F : Type) [Group F] [Finite F],
        Function.Bijective
          (ProfiniteTwins.precomp (stageRadical conjD conjD_injective a5) F)) ∧
      IsOperatorMF (WA ⧸ stageRadical conjD conjD_injective a5) ∧
      ¬ IsOperatorMF WA ∧
      stageRadical conjD conjD_injective a5 ≠ ⊥ :=
  ProfiniteTwins.wreath_twins conjD conjD_injective
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT a5_ne_one a5_mul_self
    v1G_not_mem_range hMF

end AlternatingLampLiteral
end GroupApproximation
