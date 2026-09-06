import GroupApproximation.Analysis.LIXLemmaSixGenerator

/-!
# The stage-zero algebra is the whole section algebra

`H₀ = 0`, so `E₀ = 𝟏` and the corner it cuts out is everything.  That makes
`STW59.StageAlgebra 0` the section algebra `Γ(X₀, End 𝟏²)` on the nose, and
gives the unital `*`-homomorphism that `hdiag` needs in order to land in
`CStarMat 2 (StageAlgebra 0)` after passing through cs-limit's two
identifications.

The direction built here is the one the transport needs: *into* the corner.
It exists only because the corner is the whole algebra, which is exactly
`Eproj_zero_eq_one`.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix ComplexOrder CStarAlgebra

set_option linter.unusedSectionVars false

noncomputable section

/-- `E₀ = 𝟏`, because `H₀` is indexed by `Empty`. -/
theorem Eproj_zero_eq_one : STW59.Eproj 0 = 1 := by
  rw [STW59.Eproj_def, STW59.Hproj_zero]
  ext a b
  rcases a with a | a
  · rcases b with b | b
    · simp [Matrix.one_apply]
    · exact b.elim
  · exact a.elim

/-- The unit of the stage-zero algebra is the unit of the section algebra. -/
theorem stageProj_zero_eq_one : STW59.stageProj 0 = 1 := by
  rw [STW59.stageProj, Eproj_zero_eq_one, STW59.ofFunctionMatrix_one]

/-- `1 * a * 1 = a`, stated at an abstract monoid.  Stating it here and
crossing by application is the documented cure for the section algebra, whose
bare `Mul` resolves to `ContinuousMap.instMul` rather than the ring one, so
that `one_mul` does not match syntactically in place. -/
private theorem one_mul_mul_one {A : Type*} [Monoid A] (a : A) : 1 * a * 1 = a := by
  rw [one_mul, mul_one]

/-- Every section lies in the stage-zero corner. -/
theorem mem_stageAlgebra_zero (a : STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) :
    a ∈ STW59.cornerAlgebra (STW59.stageProj 0) (STW59.isStarProjection_stageProj 0) := by
  rw [STW59.mem_stageAlgebra_iff, stageProj_zero_eq_one]
  exact one_mul_mul_one a

/-- **Every section is an element of `A₀`.**  The packaging map, which is a
bijection because `E₀ = 𝟏`. -/
def toStageZero (a : STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) :
    STW59.StageAlgebra 0 :=
  ⟨a, mem_stageAlgebra_zero a⟩

@[simp]
theorem coe_toStageZero (a : STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) :
    (toStageZero a : STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) = a := rfl

theorem toStageZero_injective : Function.Injective toStageZero :=
  fun _ _ h => congrArg Subtype.val h

theorem toStageZero_surjective : Function.Surjective toStageZero :=
  fun a => ⟨(a : STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)), rfl⟩

theorem toStageZero_one : toStageZero 1 = 1 := by
  refine STW59.corner_ext ?_
  rw [coe_toStageZero, STW59.coe_stageAlgebra_one, stageProj_zero_eq_one]

theorem toStageZero_mul (a b : STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) :
    toStageZero (a * b) = toStageZero a * toStageZero b := rfl

theorem toStageZero_add (a b : STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) :
    toStageZero (a + b) = toStageZero a + toStageZero b := rfl

theorem toStageZero_zero : toStageZero 0 = 0 := rfl

theorem toStageZero_star (a : STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) :
    toStageZero (star a) = star (toStageZero a) := rfl

theorem toStageZero_smul (c : ℂ)
    (a : STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) :
    toStageZero (c • a) = c • toStageZero a := rfl

/-- **The stage-zero packaging as a unital `*`-algebra homomorphism**, which is
what `LIX.unitaryHom` and `LIX.unitaryHom_mem_unitaryComponentOne` consume. -/
def toStageZeroHom :
    STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0) →⋆ₐ[ℂ] STW59.StageAlgebra 0 where
  toFun := toStageZero
  map_one' := toStageZero_one
  map_mul' := toStageZero_mul
  map_zero' := toStageZero_zero
  map_add' := toStageZero_add
  commutes' c := by
    refine STW59.corner_ext ?_
    rw [coe_toStageZero, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      STW59.coe_corner_smul, STW59.coe_stageAlgebra_one, stageProj_zero_eq_one]
  map_star' := toStageZero_star

@[simp]
theorem toStageZeroHom_apply (a : STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) :
    toStageZeroHom a = toStageZero a := rfl

end

end LIX
end GroupApproximation
