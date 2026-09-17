import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.MarkedGroups
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import Mathlib.Algebra.Group.Pointwise.Set.Card

/-!
# Edge expansion gives the printed vertex expansion (`thm:main`, tex l.92–100)

The corpus form of `thm:main` (`SimpleKazhdanSofic.MainAssembly`) has a finite index type `ι`, the
convergence `IsMarkedLimit s σ`, and the *edge* expansion `IsExpanderFamily σ`: at least `ε |S|` pairs
`(x, i)` with `x ∈ S` and `σ_i x ∉ S`.  The printed definition (tex l.92–98) counts *neighbours*
`x q_i^{±1}` outside `S` (gap report, Lane 1, "M1 bridge").

For `S ⊆ H` with `2|S| ≤ |H|`, apply the edge expansion to `S⁻¹`.  Every left edge `x ↦ σ_i x`
leaving `S⁻¹` gives the right neighbour `(σ_i x)⁻¹ = x⁻¹ σ_i⁻¹` of `x⁻¹ ∈ S` outside `S`, and
`(x, i) ↦ ((σ_i x)⁻¹, i)` is injective.  So `ε |S| ≤ #edges ≤ m |N(S) \ S|`, and `ε / (m + 1)` is a
vertex-expansion constant.

* `expanderLimit_of_markedLimit_expanderFamily`: the printed expander limit after reindexing
  by `ι ≃ Fin m`;
* `exists_isExpanderLimit_of_markedLimit_expanderFamily`;
* `isExpanderLimitOfClass_of_markedLimit_expanderFamily`: groups from a class `C`.
-/

namespace GroupApproximation.Full.SK01

open Filter
open scoped Pointwise

/-- Reindexing the generators by an equivalence reindexes the words. -/
theorem lift_comp_equiv_apply {ι κ K : Type*} [Group K] (f : ι → K) (e : ι ≃ κ)
    (w : FreeGroup κ) :
    FreeGroup.lift (fun j => f (e.symm j)) w = FreeGroup.lift f (FreeGroup.map e.symm w) := by
  have h := FreeGroup.lift_unique (f := fun j => f (e.symm j))
    ((FreeGroup.lift f).comp (FreeGroup.map e.symm))
    (fun x => by rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of]) (x := w)
  rw [MonoidHom.comp_apply] at h
  exact h.symm

/-- Left edges `x ↦ σ_i x` leaving `S⁻¹` inject into pairs (right neighbour of `S` outside `S`,
letter). -/
theorem ncard_leavingEdges_inv_le {ι H : Type*} [Group H] [Finite H] (σ : ι → H) {m : ℕ}
    (e : ι ≃ Fin m) (S : Set H) :
    ({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)).ncard ≤
      (cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard * m := by
  have hmaps : ∀ p ∈ ({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)),
      (fun p : H × ι => ((σ p.2 * p.1)⁻¹, e p.2)) p ∈
        (cayleyNeighbors (fun j => σ (e.symm j)) S \ S) ×ˢ (Set.univ : Set (Fin m)) := by
    intro p hp
    obtain ⟨hy, hyi⟩ := hp
    have hnbr : (σ p.2 * p.1)⁻¹ ∈ cayleyNeighbors (fun j => σ (e.symm j)) S := by
      refine ⟨p.1⁻¹, Set.mem_inv.mp hy, e p.2, Or.inr ?_⟩
      show (σ p.2 * p.1)⁻¹ = p.1⁻¹ * (σ (e.symm (e p.2)))⁻¹
      rw [Equiv.symm_apply_apply, _root_.mul_inv_rev]
    have hout : (σ p.2 * p.1)⁻¹ ∉ S := fun hmem => hyi (Set.mem_inv.mpr hmem)
    exact Set.mk_mem_prod ⟨hnbr, hout⟩ (Set.mem_univ _)
  have hinj : Set.InjOn (fun p : H × ι => ((σ p.2 * p.1)⁻¹, e p.2))
      ({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)) := by
    intro p _ p' _ h
    have h1 : (σ p.2 * p.1)⁻¹ = (σ p'.2 * p'.1)⁻¹ := congrArg Prod.fst h
    have h2 : e p.2 = e p'.2 := congrArg Prod.snd h
    have hi : p.2 = p'.2 := e.injective h2
    rw [inv_inj, hi, mul_right_inj] at h1
    exact Prod.ext h1 hi
  have h := Set.ncard_le_ncard_of_injOn (fun p : H × ι => ((σ p.2 * p.1)⁻¹, e p.2)) hmaps hinj
  rw [Set.ncard_prod, Set.ncard_univ, Nat.card_fin] at h
  exact h

/-- Edge expansion of `S⁻¹` with constant `ε` gives vertex expansion of `S` with constant
`ε / (m + 1)`. -/
theorem expansion_transfer {ι H : Type*} [Group H] [Finite H] (σ : ι → H) {m : ℕ}
    (e : ι ≃ Fin m) {ε : ℝ} (S : Set H)
    (hbound : ε * ((S⁻¹).ncard : ℝ) ≤
      (({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)).ncard : ℝ)) :
    ε / ((m : ℝ) + 1) * (S.ncard : ℝ) ≤
      ((cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard : ℝ) := by
  have hcount := ncard_leavingEdges_inv_le σ e S
  have hcount' : (({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)).ncard : ℝ) ≤
      ((cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard : ℝ) * (m : ℝ) := by
    exact_mod_cast hcount
  rw [Set.ncard_inv S] at hbound
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hN : (0 : ℝ) ≤ ((cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard : ℝ) :=
    Nat.cast_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ hm]
  calc ε * (S.ncard : ℝ)
      ≤ (({p : H × ι | p.1 ∈ S⁻¹ ∧ σ p.2 * p.1 ∉ S⁻¹} : Set (H × ι)).ncard : ℝ) := hbound
    _ ≤ ((cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard : ℝ) * (m : ℝ) := hcount'
    _ ≤ ((cayleyNeighbors (fun j => σ (e.symm j)) S \ S).ncard : ℝ) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hN

/-- **M1 bridge** (gap report, Lane 1; tex l.92–98).  A marked limit with a family of expanders, in
the corpus form of `thm:main` (`SimpleKazhdanSofic.IsMarkedLimit`,
`SimpleKazhdanSofic.IsExpanderFamily`, edge expansion), is an expander limit in the printed sense
(vertex expansion through right products with generators and inverses), after reindexing the finite
generating family along any `e : ι ≃ Fin m`. -/
theorem expanderLimit_of_markedLimit_expanderFamily {ι G : Type*} [Group G] {s : ι → G}
    {H : ℕ → Type*} [∀ ℓ, Group (H ℓ)] {σ : ∀ ℓ, ι → H ℓ} {m : ℕ} (e : ι ≃ Fin m)
    (hlim : SimpleKazhdanSofic.IsMarkedLimit s σ) (hexp : SimpleKazhdanSofic.IsExpanderFamily σ) :
    IsExpanderLimit (fun ℓ j => σ ℓ (e.symm j)) (fun j => s (e.symm j)) := by
  obtain ⟨hs, hσ, hw⟩ := hlim
  obtain ⟨_, hfin, hcard, ε, hε, hbound⟩ := hexp
  have hmarkG : IsMarking (fun j => s (e.symm j)) := by
    show Subgroup.closure (Set.range (s ∘ e.symm)) = ⊤
    rw [e.symm.surjective.range_comp s]
    exact hs
  have hmark : ∀ ℓ, IsMarking (fun j => σ ℓ (e.symm j)) := fun ℓ => by
    show Subgroup.closure (Set.range (σ ℓ ∘ e.symm)) = ⊤
    rw [e.symm.surjective.range_comp (σ ℓ)]
    exact hσ ℓ
  have hwords : ∀ w : FreeGroup (Fin m), ∀ᶠ ℓ in atTop,
      (FreeGroup.lift (fun j => σ ℓ (e.symm j)) w = 1 ↔
        FreeGroup.lift (fun j => s (e.symm j)) w = 1) := by
    intro w
    filter_upwards [hw (FreeGroup.map e.symm w)] with ℓ hℓ
    rw [lift_comp_equiv_apply (σ ℓ) e w, lift_comp_equiv_apply s e w]
    exact hℓ
  have hexp' : ∀ (ℓ : ℕ) (S : Set (H ℓ)), 2 * S.ncard ≤ Nat.card (H ℓ) →
      ε / ((m : ℝ) + 1) * (S.ncard : ℝ) ≤
        ((cayleyNeighbors (fun j => σ ℓ (e.symm j)) S \ S).ncard : ℝ) := by
    intro ℓ S hS
    haveI := hfin ℓ
    have hS' : 2 * (S⁻¹).ncard ≤ Nat.card (H ℓ) := by
      rw [Set.ncard_inv S]
      exact hS
    exact expansion_transfer (σ ℓ) e S (hbound ℓ S⁻¹ hS')
  exact ⟨⟨hmark, hmarkG, hwords⟩, hfin, hcard, ε / ((m : ℝ) + 1),
    div_pos hε (by positivity), hexp'⟩

/-- The M1 bridge with the reindexing chosen: some marking by `Fin m` is a printed expander
limit. -/
theorem exists_isExpanderLimit_of_markedLimit_expanderFamily {ι G : Type*} [Group G] {s : ι → G}
    {H : ℕ → Type*} [∀ ℓ, Group (H ℓ)] {σ : ∀ ℓ, ι → H ℓ}
    (hlim : SimpleKazhdanSofic.IsMarkedLimit s σ) (hexp : SimpleKazhdanSofic.IsExpanderFamily σ) :
    ∃ (m : ℕ) (g : Fin m → G) (q : ∀ ℓ, Fin m → H ℓ), IsExpanderLimit q g := by
  haveI : Finite ι := hexp.1
  exact ⟨Nat.card ι, fun j => s ((Finite.equivFin ι).symm j),
    fun ℓ j => σ ℓ ((Finite.equivFin ι).symm j),
    expanderLimit_of_markedLimit_expanderFamily (Finite.equivFin ι) hlim hexp⟩

/-- The M1 bridge for a class (tex l.98–100): if the finite groups of a corpus expander family lie
in the class `C`, the marked limit is an expander limit of groups from `C` in the printed sense. -/
theorem isExpanderLimitOfClass_of_markedLimit_expanderFamily
    {C : ∀ (Q : Type) [Group Q], Prop} {ι G : Type*} [Group G] {s : ι → G}
    {H : ℕ → Type} [∀ ℓ, Group (H ℓ)] {σ : ∀ ℓ, ι → H ℓ} (hC : ∀ ℓ, C (H ℓ))
    (hlim : SimpleKazhdanSofic.IsMarkedLimit s σ) (hexp : SimpleKazhdanSofic.IsExpanderFamily σ) :
    IsExpanderLimitOfClass C G := by
  haveI : Finite ι := hexp.1
  exact ⟨Nat.card ι, fun j => s ((Finite.equivFin ι).symm j), H, inferInstance,
    fun ℓ j => σ ℓ ((Finite.equivFin ι).symm j), hC,
    expanderLimit_of_markedLimit_expanderFamily (Finite.equivFin ι) hlim hexp⟩

end GroupApproximation.Full.SK01

#audit_axioms GroupApproximation.Full.SK01.expanderLimit_of_markedLimit_expanderFamily
#audit_axioms GroupApproximation.Full.SK01.isExpanderLimitOfClass_of_markedLimit_expanderFamily
