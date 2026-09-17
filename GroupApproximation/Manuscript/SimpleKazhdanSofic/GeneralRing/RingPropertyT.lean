import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRing.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# "The ring and property (T)" in `simple_kazhdan_sofic_group.tex`

Subsection "The ring and property (T)" of Section `sec:proof` (tex l.222–238):

> (l.223) Write $e_U$ for the indicator of a clopen set $U\subseteq C$.
>
> (l.223–226) The ring $R=\bigoplus_{\xi\in\Lambda}\LC(C,\F_2)\,u_\xi$ has the multiplication
> $(fu_\xi)(f'u_\eta)=f\,(f'\circ\xi^{-1})\,u_{\xi\eta}$, so $u_\xi e_Uu_\xi^{-1}=e_{\xi U}$.
>
> (l.231–233, `eq:elementary`) $e_{ij}(r+r')=e_{ij}(r)e_{ij}(r')$,
> $[e_{il}(r),e_{lj}(r')]=e_{ij}(rr')$.
>
> (l.234–237) By Ershov and Jaikin-Zapirain [Theorem 1.1], $\EL_n$ of every finitely generated
> associative unital ring has property (T) for $n\ge3$, so $G$ has property (T).
>
> (l.237–238) It is infinite because $e_{12}(\LC(C,\F_2))$ is infinite.

## Formalization

* `clopenIndicator Λ hU`: `e_U = charFn U · u_1` in `R = ClopenGroupCrossedProduct Λ C (ZMod 2)`;
  as a function on `C` it is `Set.indicator U 1` (`manuscriptSentence_clopenIndicator`).
* The direct-sum decomposition, the multiplication rule and `u_ξ e_U u_ξ⁻¹ = e_{ξU}`:
  `manuscriptSentence_groupCrossedProductMultiplication`.
* `eq:elementary` in every rank: `manuscriptSentence_elementaryIdentities`, with
  `⁅g, h⁆ = g h g⁻¹ h⁻¹` (Mathlib's `commutatorElement`).
* Ershov--Jaikin-Zapirain: `manuscriptSentence_ejzPropertyT`, both the general theorem and its
  application to `G = EL_n(R)` in the setting of `thm:general`.
* Infiniteness: `manuscriptSentence_elementaryGroupInfinite`.

## Proof route

* The ring: `printedGroupCrossedProductRing` (`GeneralRingPropertyT`), from the skew monoid algebra
  API of `ClopenGroupCrossedProduct`.
* `eq:elementary`: `printedGeneralElementaryIdentities` (`elementaryUnit_mul`,
  `elementaryUnit_commutator`).
* EJZ: `printedEJZTheorem`, which is
  `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`, proved in this
  repository (no hypothesis); a finite generating set `S` of `R` makes `R` finitely generated.
* Infinite: a Cantor set is infinite (`infinite_of_perfectSpace`) and totally separated, so
  `LC(C, F₂)` is infinite (`infinite_locallyConstant_zmodTwo`), and `f ↦ e_ij(f u_1)` is injective
  (`ClopenGroupCrossedProduct.coeff_injective`, `elementaryUnit_injective`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace GeneralRing

open scoped commutatorElement

/-! ## Indicators (tex l.223) -/

/-- **`e_U`** (tex l.223): the indicator of a clopen set `U ⊆ C`, as the element `charFn U · u_1` of
`R = LC(C, F₂) ⋊ Λ`. -/
noncomputable def clopenIndicator (Λ : Type) [Group Λ] {C : Type} [TopologicalSpace C]
    [MulAction Λ C] [ContinuousConstSMul Λ C] {U : Set C} (hU : IsClopen U) :
    ClopenGroupCrossedProduct Λ C (ZMod 2) :=
  ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) (LocallyConstant.charFn (ZMod 2) hU)

/-- **`e_U` is the indicator of `U`** (tex l.223): the locally constant function underlying `e_U` is
`1` on `U` and `0` off `U`. -/
theorem manuscriptSentence_clopenIndicator :
    ∀ (C : Type) [TopologicalSpace C] (U : Set C) (hU : IsClopen U),
      (LocallyConstant.charFn (ZMod 2) hU : C → ZMod 2) = Set.indicator U 1 := by
  intro C _ U hU
  exact LocallyConstant.coe_charFn (ZMod 2) hU

/-! ## The ring (tex l.223–226) -/

/-- `u_ξ e_U u_ξ⁻¹ = e_{ξU}`. -/
theorem unit_mul_clopenIndicator_mul_inv (Λ : Type) [Group Λ] {C : Type} [TopologicalSpace C]
    [MulAction Λ C] [ContinuousConstSMul Λ C] (ξ : Λ) {U : Set C} (hU : IsClopen U) :
    (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ : ClopenGroupCrossedProduct Λ C (ZMod 2)) *
        clopenIndicator Λ hU *
        ((ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ)⁻¹ :
          (ClopenGroupCrossedProduct Λ C (ZMod 2))ˣ) =
      clopenIndicator Λ (ClopenGroupCrossedProduct.isClopen_smul_set Λ C ξ hU) :=
  ClopenGroupCrossedProduct.unit_mul_charFn_mul_inv Λ C (ZMod 2) ξ hU

/-- **The ring** (tex l.223–226): for a group `Λ` acting by homeomorphisms on `C`,
`R = ⊕_{ξ ∈ Λ} LC(C, F₂) u_ξ` (every element is a finite sum `∑ f_ξ u_ξ`, and the coefficients of
such a sum are determined), `(f u_ξ)(f' u_η) = f (f' ∘ ξ⁻¹) u_{ξη}`, and `u_ξ e_U u_ξ⁻¹ = e_{ξU}`. -/
theorem manuscriptSentence_groupCrossedProductMultiplication :
    ∀ (Λ : Type) [Group Λ] (C : Type) [TopologicalSpace C] [MulAction Λ C]
      [ContinuousConstSMul Λ C],
      (∀ r : ClopenGroupCrossedProduct Λ C (ZMod 2),
        ∃ (T : Finset Λ) (f : Λ → LocallyConstant C (ZMod 2)),
          r = ∑ ξ ∈ T, ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) (f ξ) *
            (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ :
              ClopenGroupCrossedProduct Λ C (ZMod 2))) ∧
      (∀ (T : Finset Λ) (f g : Λ → LocallyConstant C (ZMod 2)),
        ∑ ξ ∈ T, ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) (f ξ) *
            (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ :
              ClopenGroupCrossedProduct Λ C (ZMod 2)) =
          ∑ ξ ∈ T, ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) (g ξ) *
            (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ :
              ClopenGroupCrossedProduct Λ C (ZMod 2)) →
        ∀ ξ ∈ T, f ξ = g ξ) ∧
      (∀ (ξ η : Λ) (f f' : LocallyConstant C (ZMod 2)),
        (ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) f *
            (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ :
              ClopenGroupCrossedProduct Λ C (ZMod 2))) *
          (ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) f' *
            (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) η :
              ClopenGroupCrossedProduct Λ C (ZMod 2))) =
        ClopenGroupCrossedProduct.coeff Λ C (ZMod 2)
            (f * LocallyConstant.comap (ClopenGroupCoeff.smulMap Λ C ξ⁻¹) f') *
          (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) (ξ * η) :
            ClopenGroupCrossedProduct Λ C (ZMod 2))) ∧
      (∀ (ξ : Λ) (U : Set C) (hU : IsClopen U),
        (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ : ClopenGroupCrossedProduct Λ C (ZMod 2)) *
            clopenIndicator Λ hU *
            ((ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ)⁻¹ :
              (ClopenGroupCrossedProduct Λ C (ZMod 2))ˣ) =
          clopenIndicator Λ (ClopenGroupCrossedProduct.isClopen_smul_set Λ C ξ hU)) := by
  intro Λ _ C _ _ _
  obtain ⟨h1, h2, h3, -⟩ := printedGroupCrossedProductRing Λ C
  exact ⟨h1, h2, h3, fun ξ _ hU => unit_mul_clopenIndicator_mul_inv Λ ξ hU⟩

/-! ## `eq:elementary` (tex l.231–233) -/

/-- **`eq:elementary`** (tex l.231–233), in every rank and over every ring: for `i ≠ j`,
`e_ij(r + r') = e_ij(r) e_ij(r')`, and for distinct `i, j, l`, `[e_il(r), e_lj(r')] = e_ij(r r')`,
with `[g, h] = g h g⁻¹ h⁻¹`. -/
theorem manuscriptSentence_elementaryIdentities :
    ∀ (A : Type) [Ring A] (n : ℕ) (i j l : Fin n) (hij : i ≠ j) (hil : i ≠ l) (hlj : l ≠ j)
      (r r' : A),
      elementaryUnit i j hij (r + r') = elementaryUnit i j hij r * elementaryUnit i j hij r' ∧
        ⁅elementaryUnit i l hil r, elementaryUnit l j hlj r'⁆ = elementaryUnit i j hij (r * r') :=
  printedGeneralElementaryIdentities

/-! ## Property (T) (tex l.234–237) -/

/-- **Ershov--Jaikin-Zapirain** (tex l.234–237): `EL_n` of every finitely generated associative
unital ring has property (T) for `n ≥ 3`; so in the setting of `thm:general`, where the finite set
`S` generates `R`, `G = EL_n(R)` has property (T) for `n ≥ 3`. -/
theorem manuscriptSentence_ejzPropertyT :
    (∀ (A : Type) [Ring A], (∃ s : Finset A, Subring.closure (s : Set A) = ⊤) →
      ∀ n : ℕ, 3 ≤ n → HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin n) A)) ∧
    ∀ (Λ : Type) [Group Λ] (C : Type) [TopologicalSpace C] [MulAction Λ C]
      [ContinuousConstSMul Λ C] (S : Finset (ClopenGroupCrossedProduct Λ C (ZMod 2))),
      IsGeneralSetting Λ C S → ∀ n : ℕ, 3 ≤ n →
        HasKazhdanPropertyT.{0, 0}
          ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))) := by
  refine ⟨fun A _ hA n hn => printedEJZTheorem A hA n hn, ?_⟩
  intro Λ _ C _ _ _ S hset n hn
  obtain ⟨-, -, -, hS⟩ := hset
  exact printedEJZTheorem (ClopenGroupCrossedProduct Λ C (ZMod 2)) ⟨S, hS⟩ n hn

/-! ## Infiniteness (tex l.237–238) -/

/-- **Infiniteness** (tex l.237–238): for a Cantor set `C` and distinct indices `i, j`,
`e_ij(LC(C, F₂))` is infinite, and so `EL_n(R)` is infinite. -/
theorem manuscriptSentence_elementaryGroupInfinite :
    ∀ (Λ : Type) [Group Λ] (C : Type) [TopologicalSpace C] [CompactSpace C]
      [TopologicalSpace.MetrizableSpace C] [TotallyDisconnectedSpace C] [PerfectSpace C]
      [Nonempty C] [MulAction Λ C] [ContinuousConstSMul Λ C] (n : ℕ) (i j : Fin n)
      (hij : i ≠ j),
      (Set.range fun f : LocallyConstant C (ZMod 2) =>
          elementaryUnit i j hij (ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) f)).Infinite ∧
        Infinite ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))) := by
  intro Λ _ C _ _ _ _ _ _ _ _ n i j hij
  haveI : Infinite C := infinite_of_perfectSpace C
  haveI := infinite_locallyConstant_zmodTwo C
  have hinj : Function.Injective fun f : LocallyConstant C (ZMod 2) =>
      elementaryUnit i j hij (ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) f) := by
    intro f g hfg
    exact ClopenGroupCrossedProduct.coeff_injective Λ C (ZMod 2)
      (elementaryUnit_injective i j hij hfg)
  refine ⟨Set.infinite_range_of_injective hinj, Infinite.of_injective
    (fun f : LocallyConstant C (ZMod 2) =>
      (⟨elementaryUnit i j hij (ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) f),
        elementaryUnit_mem i j hij (ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) f)⟩ :
        ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))))) ?_⟩
  intro f g hfg
  exact hinj (congrArg Subtype.val hfg)

end GeneralRing
end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.GeneralRing.manuscriptSentence_clopenIndicator
#audit_axioms GroupApproximation.SimpleKazhdanSofic.GeneralRing.unit_mul_clopenIndicator_mul_inv
#audit_axioms GroupApproximation.SimpleKazhdanSofic.GeneralRing.manuscriptSentence_groupCrossedProductMultiplication
#audit_axioms GroupApproximation.SimpleKazhdanSofic.GeneralRing.manuscriptSentence_elementaryIdentities
#audit_axioms GroupApproximation.SimpleKazhdanSofic.GeneralRing.manuscriptSentence_ejzPropertyT
#audit_axioms GroupApproximation.SimpleKazhdanSofic.GeneralRing.manuscriptSentence_elementaryGroupInfinite
