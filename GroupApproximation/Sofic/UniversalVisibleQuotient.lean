import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.ThreeRadicalsCoincide
import GroupApproximation.Sofic.RadicalFunctoriality

/-!
# The visible quotient is universal: Hom-sets are unchanged by killing a radical

Sections 42 and 53 of the ascending-HNN dossier assert more than "the radical is
the kernel of the universal MF quotient".  They assert that for each individual
target class, *precomposition with the quotient map is a bijection on Hom-sets*.
That is the statement which makes the split epimorphism of the perfect-lamp twin
pair invisible to every approximation target at once, and it is what forces the
profinite and Bohr completions to agree.

None of that needs the concrete family, or coronas, or even a radical.  It is a
statement about any normal subgroup that every homomorphism to the target class
already kills:

* precomposition is injective because the quotient map is surjective;
* precomposition is surjective because such a homomorphism factors.

The two instantiations recorded here are the ones the dossier uses.  A
homomorphism into a countable MF group kills the MF radical (§42.5), and a
homomorphism into a residually finite group kills the finite residual (§42.4);
in each case the Hom-set of the group and of its visible quotient are in
canonical bijection.

The point of stating it this way is negative as much as positive.  A bijection
on Hom-sets into every target in the family does **not** make the quotient map
an isomorphism, so this collection of approximation targets is not jointly
conservative -- which is exactly how a non-MF group and an MF group can have
the same visible theory.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G]

/-! ## The abstract bijection -/

/-- Precomposition with a quotient map is injective, because the quotient map
is surjective.  No hypothesis on `R` beyond normality. -/
theorem comp_mk'_injective (R : Subgroup G) [R.Normal] {T : Type v} [Group T] :
    Function.Injective
      (fun F : (G ⧸ R) →* T => F.comp (QuotientGroup.mk' R)) := by
  intro F₁ F₂ h
  ext g
  exact DFunLike.congr_fun h g

/-- Precomposition with the quotient map is surjective exactly when every
homomorphism to the target already kills `R`. -/
theorem comp_mk'_surjective (R : Subgroup G) [R.Normal] {T : Type v} [Group T]
    (hker : ∀ f : G →* T, R ≤ f.ker) :
    Function.Surjective
      (fun F : (G ⧸ R) →* T => F.comp (QuotientGroup.mk' R)) := by
  intro f
  refine ⟨QuotientGroup.lift R f (hker f), ?_⟩
  ext g
  simp

/-- **The universal-quotient bijection.**  If every homomorphism `G → T` kills
`R`, then the homomorphisms `G → T` are exactly the homomorphisms `G ⧸ R → T`,
canonically. -/
theorem comp_mk'_bijective (R : Subgroup G) [R.Normal] {T : Type v} [Group T]
    (hker : ∀ f : G →* T, R ≤ f.ker) :
    Function.Bijective
      (fun F : (G ⧸ R) →* T => F.comp (QuotientGroup.mk' R)) :=
  ⟨comp_mk'_injective R, comp_mk'_surjective R hker⟩

/-! ## The two instantiations the dossier uses -/

/-- **A homomorphism into a countable MF group kills the MF radical.**  Compose
a faithful corona representation of the target with the map: the composite is a
corona representation of the source, so it kills the radical, and faithfulness
transports that back.  Stated through functoriality of the radical, which is
the same argument in one line. -/
theorem actualCoronaMFResidual_le_ker_of_isCDEOperatorMF
    {P : Type v} [Group P] [Countable P] (f : G →* P) (hP : IsCDEOperatorMF P) :
    actualCoronaMFResidual G ≤ f.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have hmap : f x ∈ (actualCoronaMFResidual G).map f :=
    Subgroup.mem_map_of_mem f hx
  have hin : f x ∈ actualCoronaMFResidual P :=
    map_actualCoronaMFResidual_le f hmap
  rw [isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hP,
    Subgroup.mem_bot] at hin
  exact hin

/-- **§42.5.**  Every countable MF target sees `G` and `G ⧸ Res_MF(G)` as the
same group, in the sense that their Hom-sets into it correspond canonically. -/
theorem comp_mk'_bijective_of_isCDEOperatorMF_target
    {P : Type v} [Group P] [Countable P] (hP : IsCDEOperatorMF P) :
    Function.Bijective
      (fun F : (G ⧸ actualCoronaMFResidual G) →* P =>
        F.comp (QuotientGroup.mk' (actualCoronaMFResidual G))) :=
  comp_mk'_bijective _
    (fun f => actualCoronaMFResidual_le_ker_of_isCDEOperatorMF f hP)

/-- **§42.4.**  The same for residually finite targets and the finite
residual. -/
theorem comp_mk'_bijective_of_isResiduallyFinite_target
    {P : Type v} [Group P] (hP : IsResiduallyFinite P) :
    Function.Bijective
      (fun F : (G ⧸ finiteResidual G) →* P =>
        F.comp (QuotientGroup.mk' (finiteResidual G))) :=
  -- `RadicalFunctoriality.finiteResidual_normal` supplies the normality instance
  comp_mk'_bijective _ (fun f => finiteResidual_le_ker f hP)

/-- **The non-conservativity reading.**  Even when precomposition is bijective
for every target in a family, the quotient map need not be injective: the
bijection says the family cannot see `R`, not that `R` is trivial.  This is the
formal content of the perfect-lamp twin pair, where the quotient is MF and the
source is not. -/
theorem exists_ne_one_of_ker_ne_bot (R : Subgroup G) (hR : R ≠ ⊥) :
    ∃ x : G, x ∈ R ∧ x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact hR (le_antisymm (fun x hx => Subgroup.mem_bot.mpr (hcon x hx)) bot_le)

end GroupApproximation
