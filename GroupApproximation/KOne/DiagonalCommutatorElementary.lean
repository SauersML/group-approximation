import GroupApproximation.KOne.UnstableKOneAbelian

/-!
# A unit-group commutator is elementary once diagonally embedded

`AGPStepOne` is given `v ∈ commutator Rˣ` (from `κ v = 1` and `κ.ker =
commutator Rˣ`) and needs a rank `n ≥ 2` at which `diag(v, 1, …, 1)` is an
elementary matrix — the printed "by the definition of `K₁`" step.  In this
development `κ` is an abstract homomorphism with `ker = commutator Rˣ`, not a
literal stabilisation colimit, so that step has to be proved from `commutator
Rˣ` directly rather than unfolded from a definition.

`BlockWhitehead.lean`'s `diagAtHom` (`u ↦ diagAt l u`, a group homomorphism
`Rˣ →* (Matrix ι ι R)ˣ`) carries `commutator Rˣ` into `commutator (Matrix ι ι
R)ˣ` (`Subgroup.map_commutator`, since diagonal matrices multiply entrywise),
and `UnstableKOneAbelian.commutator_le_elementaryGroup` carries that into
`elementaryGroup ι R`, for any nontrivial strongly divisible `R` and any two
distinct indices.
-/

namespace GroupApproximation
namespace RankNElimination

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

/-- **A commutator of `Rˣ`, diagonally embedded, is a commutator of
`(Matrix ι ι R)ˣ`.** -/
theorem diagAt_mem_commutator_of_mem {v : Rˣ} (hv : v ∈ commutator Rˣ) (l : ι) :
    diagAt l v ∈ commutator (Matrix ι ι R)ˣ := by
  have hmap : Subgroup.map (diagAtHom l) (commutator Rˣ) ≤ commutator (Matrix ι ι R)ˣ := by
    show Subgroup.map (diagAtHom l) ⁅(⊤ : Subgroup Rˣ), ⊤⁆
      ≤ ⁅(⊤ : Subgroup (Matrix ι ι R)ˣ), ⊤⁆
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hmem : diagAtHom l v ∈ Subgroup.map (diagAtHom l) (commutator Rˣ) := ⟨v, hv, rfl⟩
  rw [diagAtHom_apply] at hmem
  exact hmap hmem

/-- **The commutator-to-elementary step.**  For any nontrivial strongly
divisible `R` and two distinct indices `l m`, every `v ∈ commutator Rˣ`
diagonally embeds into `EL_ι(R)`. -/
theorem diagAt_mem_elementaryGroup_of_mem_commutator [Nontrivial R]
    (hdiv : HasSingleSandwichDivision R) {v : Rˣ} (hv : v ∈ commutator Rˣ)
    {l m : ι} (hlm : l ≠ m) : diagAt l v ∈ elementaryGroup ι R :=
  commutator_le_elementaryGroup hdiv hlm (diagAt_mem_commutator_of_mem hv l)

end RankNElimination
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.RankNElimination.diagAt_mem_commutator_of_mem
#audit_axioms GroupApproximation.RankNElimination.diagAt_mem_elementaryGroup_of_mem_commutator
