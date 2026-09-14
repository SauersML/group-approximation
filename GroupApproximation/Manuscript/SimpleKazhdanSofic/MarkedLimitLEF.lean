import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Sofic.LEF
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Order.Filter.Finite

/-!
# A marked limit of finite groups is LEF

`simple_kazhdan_sofic_group.tex` at 9047d0d3c, section "Finite models" (tex l.177–180):

> So these finite simple groups converge to $G$ in the space of marked
> groups~\cite{Grigorchuk,Champetier}, and $G$ is LEF.

Convergence in the space of marked groups is `IsMarkedLimit s σ` (`SimpleKazhdanSofic.MainAssembly`):
every word in the generators is, for all large `ℓ`, trivial in `H ℓ` exactly when it is trivial in
`G`.  Given a finite subset `F ⊆ G`, write each of its elements as a word.  Distinct elements differ by
a nontrivial word, and a product that stays in `F` gives a trivial word.  Only finitely many words are
involved, so for one large `ℓ` all of them behave in `H ℓ` as in `G`.  Evaluating the words in `H ℓ`
is then injective on `F` and multiplicative on the products that stay in `F`.

* `isTextbookLEF_of_isMarkedLimit`, `isLEF_of_isMarkedLimit`;
* `printedMarkedLimitLEFStatement : PrintedMarkedLimitLEFStatement`, the closed piece consumed by
  `printedSimpleKazhdanSoficMain_of_pieces`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open Filter

/-- **A marked limit of finite groups is LEF**, in the textbook form: evaluating fixed words in a late
finite group is injective on `F` and multiplicative on the products that stay in `F`. -/
theorem isTextbookLEF_of_isMarkedLimit {ι G : Type*} [Group G] {s : ι → G} {H : ℕ → Type}
    [∀ ℓ, Group (H ℓ)] {σ : ∀ ℓ, ι → H ℓ} (hfin : ∀ ℓ, Finite (H ℓ))
    (hlim : IsMarkedLimit s σ) : IsTextbookLEF G := by
  classical
  intro F
  obtain ⟨hs, -, hw⟩ := hlim
  have hsurj : ∀ g : G, ∃ w : FreeGroup ι, FreeGroup.lift s w = g := fun g => by
    have hg : g ∈ (FreeGroup.lift s).range := by
      rw [FreeGroup.range_lift_eq_closure, hs]
      exact Subgroup.mem_top g
    exact MonoidHom.mem_range.mp hg
  choose word hword using hsurj
  -- distinct elements of `F` stay distinct in late finite groups
  have hsep : ∀ᶠ ℓ in atTop, ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      FreeGroup.lift (σ ℓ) (word x * (word y)⁻¹) ≠ 1 := by
    refine (eventually_all_finset F).2 fun x _ => (eventually_all_finset F).2 fun y _ => ?_
    by_cases hxy : x = y
    · exact Eventually.of_forall fun _ hne => absurd hxy hne
    · refine (hw (word x * (word y)⁻¹)).mono fun ℓ hℓ _ h1 => hxy ?_
      have h2 := hℓ.mp h1
      rw [map_mul, map_inv, hword, hword] at h2
      exact mul_inv_eq_one.mp h2
  -- products are preserved in late finite groups
  have hprod : ∀ᶠ ℓ in atTop, ∀ x ∈ F, ∀ y ∈ F,
      FreeGroup.lift (σ ℓ) (word x * word y * (word (x * y))⁻¹) = 1 := by
    refine (eventually_all_finset F).2 fun x _ => (eventually_all_finset F).2 fun y _ => ?_
    refine (hw (word x * word y * (word (x * y))⁻¹)).mono fun ℓ hℓ => hℓ.mpr ?_
    rw [map_mul, map_mul, map_inv, hword, hword, hword, mul_inv_cancel]
  obtain ⟨ℓ, hℓsep, hℓprod⟩ := (hsep.and hprod).exists
  let M : FiniteGroupModel :=
    { groupCarrier := H ℓ
      group := inferInstance
      fintype := @Fintype.ofFinite (H ℓ) (hfin ℓ)
      decidableEq := Classical.decEq (H ℓ) }
  refine ⟨M, fun x => (FreeGroup.lift (σ ℓ) (word x) : H ℓ), ?_, ?_⟩
  · intro x hx y hy hxy
    by_contra hne
    have hxy' : FreeGroup.lift (σ ℓ) (word x) = FreeGroup.lift (σ ℓ) (word y) := hxy
    have h1 := hℓsep x hx y hy hne
    rw [map_mul, map_inv] at h1
    exact h1 (mul_inv_eq_one.mpr hxy')
  · intro x hx y hy _
    show FreeGroup.lift (σ ℓ) (word (x * y)) =
      FreeGroup.lift (σ ℓ) (word x) * FreeGroup.lift (σ ℓ) (word y)
    have h1 := hℓprod x hx y hy
    rw [map_mul, map_mul, map_inv] at h1
    exact (mul_inv_eq_one.mp h1).symm

/-- **A marked limit of finite groups is LEF** (tex l.177–180). -/
theorem isLEF_of_isMarkedLimit {ι G : Type*} [Group G] {s : ι → G} {H : ℕ → Type}
    [∀ ℓ, Group (H ℓ)] {σ : ∀ ℓ, ι → H ℓ} (hfin : ∀ ℓ, Finite (H ℓ))
    (hlim : IsMarkedLimit s σ) : IsLEF G :=
  (isLEF_iff_textbook G).mpr (isTextbookLEF_of_isMarkedLimit hfin hlim)

/-- The piece `PrintedMarkedLimitLEFStatement` of `thm:main`, closed. -/
theorem printedMarkedLimitLEFStatement : PrintedMarkedLimitLEFStatement := by
  intro ι G _ s H _ σ hfin hlim
  exact isLEF_of_isMarkedLimit hfin hlim

end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.isLEF_of_isMarkedLimit
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedMarkedLimitLEFStatement
