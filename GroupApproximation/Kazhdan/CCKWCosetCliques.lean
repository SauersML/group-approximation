import GroupApproximation.Kazhdan.CCKWCosetComplex

/-!
# Cliques of the coset complex of `GHB(7)`, and the fixed-vertex conclusion of CCKW 3.1(ii)

Adjacent vertices of the coset complex have different types, and there are three types.  So
the complex has no `4`-clique (`cosetComplex_cliqueFree_four`), and a clique carries each type
at most once.  An element of `GHB(7)` that maps a clique into itself preserves types, so it
fixes every vertex of the clique (`cosetAction_eq_of_mem_clique`), and a fixed vertex `kPᵢ`
gives `k⁻¹ g k ∈ Pᵢ`.

`cckwFiniteOrderConjugateIntoVertex_of_invariantCliques` is the resulting last step of CCKW
Theorem 3.1(ii) in its cyclic case: once every element of finite order maps some nonempty
clique into itself (the fixed-clique theorem for the systolic complex, `GGT/Systolic*`), every
element of finite order is conjugate into a vertex group.
-/

namespace GroupApproximation
namespace KMSGroup
namespace CCKW

theorem type_ne_of_adj {x y : Vertex} (h : cosetComplex.G.Adj x y) : x.1 ≠ y.1 := h.1

/-- **The coset complex of `GHB(7)` has no `4`-clique**: a clique has pairwise distinct types. -/
theorem cosetComplex_cliqueFree_four : cosetComplex.G.CliqueFree 4 := by
  intro t ht
  have hinj : Set.InjOn Sigma.fst (t : Set Vertex) := by
    intro x hx y hy hxy
    by_contra hne
    exact type_ne_of_adj (ht.isClique hx hy hne) hxy
  have hle := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (Fin 3))) Sigma.fst
    (fun x _ => Finset.mem_univ x.1) hinj
  rw [ht.card_eq, Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- **An element mapping a clique into itself fixes each of its vertices.** -/
theorem cosetAction_eq_of_mem_clique {σ : Finset Vertex}
    (hσ : cosetComplex.G.IsClique (σ : Set Vertex)) {g : GHB 7} {x : Vertex} (hx : x ∈ σ)
    (hgx : cosetAction g x ∈ σ) : cosetAction g x = x := by
  by_contra hne
  exact type_ne_of_adj (hσ hgx hx hne) (cosetAction_fst g x)

theorem fin_three_cases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by
  decide +kernel

/-- **CCKW Theorem 3.1(ii), cyclic case, from invariant cliques.** -/
theorem cckwFiniteOrderConjugateIntoVertex_of_invariantCliques
    (hfix : ∀ g : GHB 7, IsOfFinOrder g → ∃ σ : Finset Vertex, σ.Nonempty ∧
      cosetComplex.G.IsClique (σ : Set Vertex) ∧ ∀ x ∈ σ, cosetAction g x ∈ σ) :
    CCKWFiniteOrderConjugateIntoVertex := by
  intro g hg
  obtain ⟨σ, ⟨x, hx⟩, hσ, hinv⟩ := hfix g hg
  obtain ⟨k, hk⟩ := conj_mem_of_cosetAction_eq (cosetAction_eq_of_mem_clique hσ hx (hinv x hx))
  refine ⟨k, ?_⟩
  rcases fin_three_cases x.1 with h | h | h
  · rw [h] at hk
    exact Or.inl hk
  · rw [h] at hk
    exact Or.inr (Or.inl hk)
  · rw [h] at hk
    exact Or.inr (Or.inr hk)

end CCKW
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.CCKW.cosetComplex_cliqueFree_four
#audit_axioms GroupApproximation.KMSGroup.CCKW.cosetAction_eq_of_mem_clique
#audit_axioms GroupApproximation.KMSGroup.CCKW.cckwFiniteOrderConjugateIntoVertex_of_invariantCliques
