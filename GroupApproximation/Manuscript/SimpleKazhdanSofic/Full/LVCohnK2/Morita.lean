import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.MoritaProjection
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Card

/-!
# Morita invariance of stable `K₂` triviality (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  The ultramatricial
stages of the Cohn algebra (Ara–Brustenga–Cortiñas 2009) are products of matrix rings over `F₂`,
so we need `K₂(M_m(R)) = K₂(R)` in the form: if `R` has trivial stable `K₂` then so does
`M_m(R)` (`stableK2Trivial_matrix`).

Proof: a class `k ∈ K₂(n, M_m(R))`, padded to rank `n + 4`, is `blockMap g` for some
`g ∈ St_{(n+4) × m}(R)` with `projection g = 1`.  Relabelling `(n+4) × m ≅ (n+4)m`, stable
triviality over `R` kills `g` after padding to some `N₀`.  Since `j + m i` is compatible with
padding the first factor, `g` already dies in `St_{(N₀+4) × m}(R)`, and hence `k` dies in
`St_{N₀+4}(M_m(R))` by `blockMap_indexMap`.
-/

namespace GroupApproximation.Full.LVCohnK2

open SteinbergGroup

variable {R : Type*} [Ring R]

/-- Root elements with propositionally equal indices agree.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem x_congr {I : Type*} [Fintype I] [DecidableEq I] {i i' j j' : I} (hi : i = i')
    (hj : j = j') (hij : i ≠ j) (hij' : i' ≠ j') (a : R) : x i j hij a = x i' j' hij' a := by
  subst hi
  subst hj
  rfl

/-- Two commuting squares of index embeddings induce equal composite maps.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem indexMap_indexMap_of_comm {I₁ I₂ I₃ I₄ : Type*} [Fintype I₁] [DecidableEq I₁]
    [Fintype I₂] [DecidableEq I₂] [Fintype I₃] [DecidableEq I₃] [Fintype I₄] [DecidableEq I₄]
    (e₁ : I₁ ↪ I₂) (f₁ : I₂ ↪ I₃) (e₂ : I₁ ↪ I₄) (f₂ : I₄ ↪ I₃)
    (hc : ∀ i, f₁ (e₁ i) = f₂ (e₂ i)) (g : SteinbergGroup I₁ R) :
    indexMap f₁ (indexMap e₁ g) = indexMap f₂ (indexMap e₂ g) := by
  have hh : (indexMap (R := R) f₁).comp (indexMap e₁) = (indexMap f₂).comp (indexMap e₂) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change indexMap f₁ (indexMap e₁ (x i j hij a)) = indexMap f₂ (indexMap e₂ (x i j hij a))
    rw [indexMap_x, indexMap_x, indexMap_x, indexMap_x]
    exact x_congr (hc i) (hc j) _ _ a
  exact DFunLike.congr_fun hh g

/-- The identity embedding induces the identity.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem indexMap_refl {I : Type*} [Fintype I] [DecidableEq I] (g : SteinbergGroup I R) :
    indexMap (Function.Embedding.refl I) g = g := by
  have hh : indexMap (R := R) (Function.Embedding.refl I) = MonoidHom.id _ := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change indexMap (Function.Embedding.refl I) (x i j hij a) = x i j hij a
    exact indexMap_x (Function.Embedding.refl I) i j hij a
  exact DFunLike.congr_fun hh g

/-- Relabelling along a bijection is injective on Steinberg groups.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem indexMap_equiv_injective {I₁ I₂ : Type*} [Fintype I₁] [DecidableEq I₁] [Fintype I₂]
    [DecidableEq I₂] (E : I₁ ≃ I₂) : Function.Injective (indexMap (R := R) E.toEmbedding) := by
  intro g₁ g₂ hg
  calc g₁ = indexMap (Function.Embedding.refl I₁) g₁ := (indexMap_refl g₁).symm
    _ = indexMap (Function.Embedding.refl I₁) (indexMap (Function.Embedding.refl I₁) g₁) :=
        (indexMap_refl _).symm
    _ = indexMap E.symm.toEmbedding (indexMap E.toEmbedding g₁) :=
        indexMap_indexMap_of_comm (Function.Embedding.refl I₁) (Function.Embedding.refl I₁)
          E.toEmbedding E.symm.toEmbedding (fun i => (E.symm_apply_apply i).symm) g₁
    _ = indexMap E.symm.toEmbedding (indexMap E.toEmbedding g₂) := by rw [hg]
    _ = indexMap (Function.Embedding.refl I₁) (indexMap (Function.Embedding.refl I₁) g₂) :=
        indexMap_indexMap_of_comm E.toEmbedding E.symm.toEmbedding (Function.Embedding.refl I₁)
          (Function.Embedding.refl I₁) (fun i => E.symm_apply_apply i) g₂
    _ = indexMap (Function.Embedding.refl I₁) g₂ := indexMap_refl _
    _ = g₂ := indexMap_refl g₂

/-- `Fin (n + 4)` has room for a fourth index.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_ne_three_fin (n : ℕ) (a b c : Fin (n + 4)) :
    ∃ d : Fin (n + 4), d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  have hcard : ({a, b, c} : Finset (Fin (n + 4))).card <
      (Finset.univ : Finset (Fin (n + 4))).card := by
    rw [Finset.card_fin]
    exact lt_of_le_of_lt Finset.card_le_three (by omega)
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or] at hd
  exact ⟨d, hd.1, hd.2.1, hd.2.2⟩

/-- The relabelling `(i, j) ↦ j + m i` commutes with padding the first factor.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem finProdFinEquiv_prodMap_castLE {n N m : ℕ} (h : n ≤ N) (h' : n * m ≤ N * m)
    (p : Fin n × Fin m) :
    (finProdFinEquiv : Fin N × Fin m ≃ Fin (N * m)).toEmbedding
        ((Fin.castLEEmb h).prodMap (Function.Embedding.refl (Fin m)) p) =
      Fin.castLEEmb h' ((finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)).toEmbedding p) :=
  Fin.ext rfl

/-- Steinberg groups over the zero ring `M_0(R)` are trivial.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem eq_one_matrix_fin_zero {I : Type*} [Fintype I] [DecidableEq I]
    (k : SteinbergGroup I (Matrix (Fin 0) (Fin 0) R)) : k = 1 := by
  have hk : k ∈ (⊥ : Subgroup (SteinbergGroup I (Matrix (Fin 0) (Fin 0) R))) := by
    refine PresentedGroup.generated_by (relations (I := I) (R := Matrix (Fin 0) (Fin 0) R)) ⊥
      ?_ k
    rintro ⟨i, j, hij, M⟩
    change x i j hij M ∈ (⊥ : Subgroup (SteinbergGroup I (Matrix (Fin 0) (Fin 0) R)))
    have hM : M = 0 := Matrix.ext fun p _ => (Nat.not_lt_zero _ p.2).elim
    rw [hM, x_zero]
    exact one_mem _
  exact Subgroup.mem_bot.mp hk

/-- **Morita invariance.**  If `R` has trivial stable `K₂`, so does `M_m(R)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, `sec:questions`, leaf T1b.iii.) -/
theorem stableK2Trivial_matrix (m : ℕ) (hR : LVH2GL3.StableK2Trivial R) :
    LVH2GL3.StableK2Trivial (Matrix (Fin m) (Fin m) R) := by
  intro n k hk
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨n, le_rfl, by rw [eq_one_matrix_fin_zero k, map_one]⟩
  · have hn : n ≤ n + 4 := Nat.le_add_right n 4
    have hk' : projection (indexMap (Fin.castLEEmb hn) k) = 1 :=
      LVH2GL3.projection_indexMap_eq_one _ hk
    obtain ⟨g, hg⟩ := blockMap_surjective (J := Fin m) (R := R) (exists_ne_three_fin n)
      (indexMap (Fin.castLEEmb hn) k)
    have hgp : projection g = 1 := by
      refine projection_eq_one_of_blockMap (exists_ne_three_fin n) g ?_
      rw [hg]
      exact hk'
    obtain ⟨N₀, hN₀, hkill⟩ := hR ((n + 4) * m)
      (indexMap (finProdFinEquiv : Fin (n + 4) × Fin m ≃ Fin ((n + 4) * m)).toEmbedding g)
      (LVH2GL3.projection_indexMap_eq_one _ hgp)
    have hn4 : n + 4 ≤ N₀ + 4 :=
      ((Nat.le_mul_of_pos_right (n + 4) hm).trans hN₀).trans (Nat.le_add_right N₀ 4)
    have h2 : N₀ ≤ (N₀ + 4) * m :=
      (Nat.le_add_right N₀ 4).trans (Nat.le_mul_of_pos_right (N₀ + 4) hm)
    have h3 : (n + 4) * m ≤ (N₀ + 4) * m := hN₀.trans h2
    have hP : indexMap ((Fin.castLEEmb hn4).prodMap (Function.Embedding.refl (Fin m))) g = 1 := by
      refine indexMap_equiv_injective (R := R)
        (finProdFinEquiv : Fin (N₀ + 4) × Fin m ≃ Fin ((N₀ + 4) * m)) ?_
      rw [map_one,
        indexMap_indexMap_of_comm
          ((Fin.castLEEmb hn4).prodMap (Function.Embedding.refl (Fin m)))
          (finProdFinEquiv : Fin (N₀ + 4) × Fin m ≃ Fin ((N₀ + 4) * m)).toEmbedding
          (finProdFinEquiv : Fin (n + 4) × Fin m ≃ Fin ((n + 4) * m)).toEmbedding
          (Fin.castLEEmb h3) (finProdFinEquiv_prodMap_castLE hn4 h3) g,
        ← LVH2GL3.indexMap_castLEEmb_castLEEmb hN₀ h2, hkill, map_one]
    refine ⟨N₀ + 4, hn.trans hn4, ?_⟩
    rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb hn hn4 k, ← hg,
      ← blockMap_indexMap (exists_ne_three_fin n) (exists_ne_three_fin N₀) (Fin.castLEEmb hn4) g,
      hP, map_one]

end GroupApproximation.Full.LVCohnK2
