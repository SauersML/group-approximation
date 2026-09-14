import GroupApproximation.Analysis.KazhdanQuotientCheeger
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite quotients of a Kazhdan group form expanders

`simple_kazhdan_sofic_group.tex` at origin/main e80dcf20a, section "Finite models", tex l.163–164:

> Since $\EL_3(F)$ has property~\textup{(T)}, their Cayley graphs form a family of
> expanders~\cite{Kassabov}.

"their" refers to the finite simple groups $\SL_{3N_\ell}(\F_2)$, quotients of $\EL_3(F)$ with
compatible generators (tex l.151–160).  The printed route is the classical one: a Kazhdan group maps
onto the finite groups, so the Kazhdan constant bounds the edge expansion of every quotient Cayley
graph.  No literature input is used; the estimate is proved in `Analysis/KazhdanQuotientCheeger`.

The conclusion is stated in the manuscript's spelling `SimpleKazhdanSofic.IsExpanderFamily σ`
(`MainAssembly`, lane ct-two-ended): the generating family is finite, the orders tend to infinity,
and some `ε > 0` bounds below the edges `x → σ_i x` leaving every set of at most half the vertices.

* `isExpanderFamily_of_hasKazhdanPropertyT_quotients`: for a Kazhdan group with a finite generating
  family `t` and surjections `π ℓ` onto finite groups of unbounded order, the Cayley graphs with
  respect to `π ℓ ∘ t` form a family of expanders.
* `PrintedKazhdanQuotientsExpanders`: the closed endpoint.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open Filter

universe u v w

/-- **Finite quotients of a Kazhdan group form expanders** (tex l.163–164).  Let `Γ` have
property (T), let the finite family `t` generate `Γ`, and let `π ℓ` map `Γ` onto finite groups whose
orders tend to infinity.  Then the Cayley graphs of the quotients with respect to the images of `t`
form a family of expanders. -/
theorem isExpanderFamily_of_hasKazhdanPropertyT_quotients {Γ : Type u} [Group Γ]
    (hT : HasKazhdanPropertyT.{u, v} Γ) {ι : Type w} [Finite ι] (t : ι → Γ)
    (ht : Subgroup.closure (Set.range t) = ⊤) {H : ℕ → Type v} [∀ ℓ, Group (H ℓ)]
    [∀ ℓ, Finite (H ℓ)] (π : ∀ ℓ, Γ →* H ℓ) (hπ : ∀ ℓ, Function.Surjective (π ℓ))
    (hcard : Tendsto (fun ℓ ↦ Nat.card (H ℓ)) atTop atTop) :
    IsExpanderFamily (fun ℓ (i : ι) ↦ π ℓ (t i)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨Q₀, ε, hQ₀⟩ := hT
  have hgen : Subgroup.closure ((Finset.univ.image t : Finset Γ) : Set Γ) = ⊤ := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ht]
  obtain ⟨δ, hδ⟩ := KazhdanQuotientCheeger.exists_isKazhdanPair_of_closure_eq_top hQ₀ _ hgen
  refine ⟨inferInstance, fun ℓ ↦ inferInstance, hcard, δ ^ 2 / 4,
    div_pos (pow_pos hδ.1 2) (by norm_num), ?_⟩
  intro ℓ S hS
  haveI : Fintype (H ℓ) := Fintype.ofFinite (H ℓ)
  set A : Finset (H ℓ) := S.toFinset with hAdef
  have hSA : S.ncard = A.card := Set.ncard_eq_toFinset_card' S
  rcases A.eq_empty_or_nonempty with hA0 | hne
  · rw [hSA, hA0]
    simp
  have hA : 2 * A.card ≤ Fintype.card (H ℓ) := by
    rw [← hSA, ← Nat.card_eq_fintype_card]
    exact hS
  obtain ⟨s, hs, hbound⟩ :=
    KazhdanQuotientCheeger.kazhdanPair_quotient_boundary hδ (π ℓ) (hπ ℓ) A hne hA
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
  have hinj : Function.Injective fun a : H ℓ ↦ (a, i) := fun a b h ↦ (Prod.mk.inj h).1
  have hsub : (fun a : H ℓ ↦ (a, i)) ''
        ((A.filter fun a ↦ π ℓ (t i) * a ∉ A : Finset (H ℓ)) : Set (H ℓ)) ⊆
      {p : H ℓ × ι | p.1 ∈ S ∧ π ℓ (t p.2) * p.1 ∉ S} := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [hAdef] using ha
  have hcardle : ((A.filter fun a ↦ π ℓ (t i) * a ∉ A).card : ℝ) ≤
      (({p : H ℓ × ι | p.1 ∈ S ∧ π ℓ (t p.2) * p.1 ∉ S} : Set (H ℓ × ι)).ncard : ℝ) := by
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset] at hle
    exact_mod_cast hle
  rw [hSA]
  exact hbound.trans hcardle

/-- **Tex l.163–164, along the printed route**: "Since $\EL_3(F)$ has property (T), their Cayley
graphs form a family of expanders".  For every group with property (T), every finite generating
family `t` and every sequence of surjections onto finite groups of unbounded order, the Cayley graphs
with respect to the images of `t` form a family of expanders. -/
def PrintedKazhdanQuotientsExpanders : Prop :=
  ∀ (Γ : Type) [Group Γ], HasKazhdanPropertyT.{0, 0} Γ →
    ∀ (ι : Type) [Finite ι] (t : ι → Γ), Subgroup.closure (Set.range t) = ⊤ →
      ∀ (H : ℕ → Type) [∀ ℓ, Group (H ℓ)] [∀ ℓ, Finite (H ℓ)] (π : ∀ ℓ, Γ →* H ℓ),
        (∀ ℓ, Function.Surjective (π ℓ)) → Tendsto (fun ℓ ↦ Nat.card (H ℓ)) atTop atTop →
          IsExpanderFamily (fun ℓ (i : ι) ↦ π ℓ (t i))

theorem printedKazhdanQuotientsExpanders : PrintedKazhdanQuotientsExpanders := by
  intro Γ _ hT ι _ t ht H _ _ π hπ hcard
  exact isExpanderFamily_of_hasKazhdanPropertyT_quotients hT t ht π hπ hcard

#audit_closed_axioms printedKazhdanQuotientsExpanders

end SimpleKazhdanSofic
end GroupApproximation
