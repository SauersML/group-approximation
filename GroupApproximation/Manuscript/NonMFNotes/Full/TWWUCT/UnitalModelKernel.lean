import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureData

/-!
# Split extensions and the kernel of a character

Lane TWWUCT-G (work order WO-TWWUCT-G), `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input).

The UCT class of Rosenberg--Schochet is defined through `KK`-equivalence to *some* separable
commutative algebra, while Tu's argument naturally places non-unital algebras (kernels, proper
crossed products) in the `KKn`-commutative class.  To pass from a unital algebra `A` with a
character `χ : A → ℂ` to a *unital* commutative model one uses the split extension
`0 → ker χ → A → ℂ → 0`, split by the unit `ℂ → A` (Blackadar, *K-Theory for Operator
Algebras*, 19.9.1 and 22.3.5; Rosenberg--Schochet, Duke Math. J. 55 (1987), §2).

Contents:
* `SplitExtension I A B`: an extension `0 → I → A → B → 0` with a `⋆`-homomorphic section,
  and `SplitExtension.toSemisplitExtension` (a `⋆`-homomorphism is a completely positive
  contraction, Blackadar 15.8);
* `characterKernel χ`: the kernel of a character `χ` of a separable unital C⋆-algebra, as a
  bundled separable non-unital C⋆-algebra;
* `characterSplitExtension χ : SplitExtension (characterKernel χ) A ℂ`.
-/

namespace GroupApproximation.Full.TWWUCT.UnitalModel

open Bootstrap

noncomputable section

/-- **A split extension** `0 → I → A → B → 0` of separable non-unital C⋆-algebras: an exact
sequence whose quotient map has a `⋆`-homomorphic section (Blackadar 19.9.1).
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
structure SplitExtension (I A B : SepNUCStarAlgebra) where
  /-- The inclusion of the ideal. -/
  incl : I →⋆ₙₐ[ℂ] A
  /-- The quotient map. -/
  quot : A →⋆ₙₐ[ℂ] B
  incl_injective : Function.Injective incl
  /-- Exactness in the middle: the kernel of `quot` is the range of `incl`. -/
  exact : ∀ a : A, quot a = 0 ↔ ∃ i : I, incl i = a
  /-- The `⋆`-homomorphic section. -/
  sec : B →⋆ₙₐ[ℂ] A
  quot_sec : ∀ b : B, quot (sec b) = b

/-- A split extension is semisplit: its `⋆`-homomorphic section is a completely positive
contractive linear section (Blackadar 15.8).  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
def SplitExtension.toSemisplitExtension {I A B : SepNUCStarAlgebra} (E : SplitExtension I A B) :
    SemisplitExtension I A B where
  incl := E.incl
  quot := E.quot
  incl_injective := E.incl_injective
  quot_surjective b := ⟨E.sec b, E.quot_sec b⟩
  exact := E.exact
  sec := (E.sec : B →ₗ[ℂ] A)
  sec_completelyPositive := CStarExactness.isCompletelyPositive_of_starAlgHom E.sec
  sec_contractive b := NonUnitalStarAlgHom.norm_apply_le E.sec b
  quot_sec b := E.quot_sec b

section Character

variable {A : Type} [CStarAlgebra A] (χ : A →⋆ₐ[ℂ] ℂ)

/-- The kernel `ker χ` of a character, as a non-unital `⋆`-subalgebra.
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
def characterKernelSubalgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | χ a = 0}
  add_mem' := fun {a b} (ha : χ a = 0) (hb : χ b = 0) =>
    show χ (a + b) = 0 by rw [map_add, ha, hb, add_zero]
  zero_mem' := show χ 0 = 0 from map_zero χ
  mul_mem' := fun {a b} (ha : χ a = 0) (_ : χ b = 0) =>
    show χ (a * b) = 0 by rw [map_mul, ha, zero_mul]
  smul_mem' := fun c {a} (ha : χ a = 0) => show χ (c • a) = 0 by rw [map_smul, ha, smul_zero]
  star_mem' := fun {a} (ha : χ a = 0) => show χ (star a) = 0 by rw [map_star, ha, star_zero]

variable {χ} in
theorem mem_characterKernelSubalgebra {a : A} : a ∈ characterKernelSubalgebra χ ↔ χ a = 0 :=
  Iff.rfl

theorem coe_characterKernelSubalgebra :
    (characterKernelSubalgebra χ : Set A) = ⇑χ ⁻¹' {0} :=
  Set.ext fun _ => Iff.rfl

/-- A character is continuous (it is a `⋆`-homomorphism of C⋆-algebras). -/
theorem continuous_character : Continuous (χ : A → ℂ) :=
  AddMonoidHomClass.continuous_of_bound χ 1 fun a => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le χ a

instance isClosed_characterKernelSubalgebra :
    IsClosed (characterKernelSubalgebra χ : Set A) := by
  rw [coe_characterKernelSubalgebra]
  exact IsClosed.preimage (continuous_character χ) isClosed_singleton

/-- The kernel of a character, as a type. -/
abbrev CharacterKernel : Type :=
  characterKernelSubalgebra χ

instance instNonUnitalCStarAlgebraCharacterKernel : NonUnitalCStarAlgebra (CharacterKernel χ) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (characterKernelSubalgebra χ)
    (h_closed := isClosed_characterKernelSubalgebra χ)

instance instSeparableSpaceCharacterKernel [TopologicalSpace.SeparableSpace A] :
    TopologicalSpace.SeparableSpace (CharacterKernel χ) := by
  have hcl : TopologicalSpace.IsSeparable (characterKernelSubalgebra χ : Set A) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  exact hcl.separableSpace

/-- **The kernel of a character** `χ : A → ℂ` of a separable unital C⋆-algebra, bundled as a
separable non-unital C⋆-algebra.  `non_mf_group_notes.tex`, `thm:fixed-radical-membership`
(UCT input). -/
def characterKernel [TopologicalSpace.SeparableSpace A] : SepNUCStarAlgebra :=
  SepNUCStarAlgebra.of (CharacterKernel χ)

/-- **The split extension of a character** `0 → ker χ → A → ℂ → 0`, split by the unital
inclusion `ℂ → A` (Blackadar 22.3.5).  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
def characterSplitExtension [TopologicalSpace.SeparableSpace A] :
    SplitExtension (characterKernel χ) (SepNUCStarAlgebra.of A) (SepNUCStarAlgebra.of ℂ) where
  incl := NonUnitalStarSubalgebra.subtype (characterKernelSubalgebra χ)
  quot := χ.toNonUnitalStarAlgHom
  incl_injective := fun _ _ h => Subtype.ext h
  exact := fun a =>
    ⟨fun h => ⟨(⟨a, h⟩ : CharacterKernel χ), rfl⟩, by
      rintro ⟨i, rfl⟩
      exact Subtype.property (i : CharacterKernel χ)⟩
  sec := (StarAlgHom.ofId ℂ A).toNonUnitalStarAlgHom
  quot_sec := fun b => AlgHomClass.commutes χ b

end Character

end

end GroupApproximation.Full.TWWUCT.UnitalModel
