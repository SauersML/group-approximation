import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.NormMFCoronaRadical

/-!
# The literal Carrión--Dadarlat--Eckhardt MF radical

This module defines invisibility by quantifying directly over homomorphisms
into the unitary groups of genuine norm-matrix C-star coronas.  Formal polar
correction identifies this literal radical with the unitary-sequence corona
radical already used by the compression argument.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G] [Countable G]

/-- An element is killed by every homomorphism into every genuine CDE
norm-matrix C-star corona with positive, strictly increasing matrix sizes. -/
def CDEMFInvisible (x : G) : Prop :=
  ∀ (X : ℕ → FiniteModel) (hne : ∀ n, Nonempty (X n)),
    letI := hne
    (∀ n, 0 < Fintype.card (X n)) →
      StrictMono (fun n ↦ Fintype.card (X n)) →
        ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)), rho x = 1

/-- The intersection of the kernels of all literal CDE-corona
representations. -/
def cdeMFResidual (G : Type u) [Group G] [Countable G] : Subgroup G where
  carrier := {x | CDEMFInvisible x}
  one_mem' := by
    intro X hne hX hmono rho
    exact map_one rho
  mul_mem' := by
    intro x y hx hy X hne hX hmono rho
    rw [map_mul, hx X hne hX hmono rho, hy X hne hX hmono rho, one_mul]
  inv_mem' := by
    intro x hx X hne hX hmono rho
    rw [map_inv, hx X hne hX hmono rho, inv_one]

@[simp] theorem mem_cdeMFResidual_iff {x : G} :
    x ∈ cdeMFResidual G ↔ CDEMFInvisible x :=
  Iff.rfl

omit [Countable G] in
/-- The literal C-star-corona and unitary-sequence invisibility predicates
coincide. -/
theorem cdeMFInvisible_iff_coronaMFInvisible {x : G} :
    CDEMFInvisible x ↔ CoronaMFInvisible x := by
  constructor
  · intro hx X hX rho
    let Y := increasingBlockModel X
    have hY : ∀ n, 0 < Fintype.card (Y n) := by
      intro n
      cases n with
      | zero => exact hX 0
      | succ n =>
          rw [show Y (n + 1) = increasingBlockModel X (n + 1) from rfl,
            card_increasingBlockModel_succ]
          exact Nat.add_pos_right _ (hX (n + 1))
    let hneY : ∀ n, Nonempty (Y n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hY n)
    letI : ∀ n, Nonempty (Y n) := hneY
    let rhoIncreasing : G →* NormMatrixCoronaUnitary Y :=
      (increasingCoronaEmbed X).comp rho
    let rhoCDE : G →* unitary (NormMatrixCStarCorona (fun n ↦ Y n)) :=
      (normMatrixCoronaUnitaryEquiv Y).toMonoidHom.comp rhoIncreasing
    have h := hx Y hneY hY (strictMono_card_increasingBlockModel X hX) rhoCDE
    apply (increasingCoronaEmbed_injective X)
    apply (normMatrixCoronaUnitaryEquiv Y).injective
    simpa [rhoIncreasing, rhoCDE] using h
  · intro hx X hne hX _hmono rho
    letI : ∀ n, Nonempty (X n) := hne
    let rhoSeq : G →* NormMatrixCoronaUnitary X :=
      (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rho
    have h := hx X hX rhoSeq
    apply (normMatrixCoronaUnitaryEquiv X).symm.injective
    simpa [rhoSeq] using h

/-- The literal CDE MF radical equals the established cofinite-corona
radical. -/
theorem cdeMFResidual_eq_coronaMFResidual :
    cdeMFResidual G = coronaMFResidual G := by
  ext x
  exact cdeMFInvisible_iff_coronaMFInvisible

/-- Hence it also equals the universal operator-norm MF residual. -/
theorem cdeMFResidual_eq_normMFResidual :
    cdeMFResidual G = normMFResidual G := by
  rw [cdeMFResidual_eq_coronaMFResidual,
    coronaMFResidual_eq_normMFResidual]

/-- A countable group is literally CDE-MF exactly when its literal radical is
trivial. -/
theorem isCDEOperatorMF_iff_cdeMFResidual_eq_bot :
    IsCDEOperatorMF G ↔ cdeMFResidual G = ⊥ := by
  rw [isCDEOperatorMF_iff_isOperatorMF,
    cdeMFResidual_eq_normMFResidual]
  exact isOperatorMF_iff_normMFResidual_eq_bot

end GroupApproximation
