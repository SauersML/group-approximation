import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Morita
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Products
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.DirectedUnion
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Interface

/-!
# Stable `K₂` of ultramatricial rings (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Ara–Brustenga–Cortiñas
2009 (Sec. 5) use that ultramatricial `𝔽₂`-rings have `K₂ = 0`: they are directed unions of finite
products of matrix rings `M_d(𝔽₂)`, and `K₂` commutes with directed unions, finite products and
matrix rings (Morita invariance).  We record:

* `stableK2Trivial_of_subsingleton`: the zero ring;
* `stableK2Trivial_pi`: finite products `∏_{j < k} A j`;
* `stableK2Trivial_matrixPi`: `∏_{j ≤ k} M_{d j}(F)` for any `F` with trivial stable `K₂`;
* `stableK2Trivial_of_isUltramatricialF2`: ultramatricial `𝔽₂`-rings, given stable `K₂(𝔽₂) = 0`
  (the latter is `LVFieldK2.stableK2Trivial_zmodTwo`, Steinberg 1962 / Milnor §10).
-/

namespace GroupApproximation.Full.LVCohnK2

open SteinbergGroup

universe u

/-- Steinberg groups over a subsingleton ring are trivial.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem eq_one_of_subsingleton {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [Ring R]
    [Subsingleton R] (k : SteinbergGroup I R) : k = 1 := by
  have hk : k ∈ (⊥ : Subgroup (SteinbergGroup I R)) := by
    refine PresentedGroup.generated_by (relations (I := I) (R := R)) ⊥ ?_ k
    rintro ⟨i, j, hij, a⟩
    change x i j hij a ∈ (⊥ : Subgroup (SteinbergGroup I R))
    rw [Subsingleton.elim a 0, x_zero]
    exact one_mem _
  exact Subgroup.mem_bot.mp hk

/-- The zero ring has trivial stable `K₂`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_of_subsingleton {R : Type*} [Ring R] [Subsingleton R] :
    LVH2GL3.StableK2Trivial R := by
  intro n k _
  exact ⟨n, le_rfl, by rw [eq_one_of_subsingleton k, map_one]⟩

/-- Splitting off the first factor: `∏_{j ≤ k} A j ≅ A 0 × ∏_{j < k} A (j + 1)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def piFinSuccRingEquiv (k : ℕ) (A : Fin (k + 1) → Type*) [∀ j, Ring (A j)] :
    ((j : Fin (k + 1)) → A j) ≃+* A 0 × ((j : Fin k) → A j.succ) where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := Prod.ext (Fin.cons_zero p.1 p.2) (funext fun j => Fin.cons_succ p.1 p.2 j)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Finite products of rings with trivial stable `K₂` have trivial stable `K₂`.
(Ara–Brustenga–Cortiñas 2009, additivity of `K`-theory, Sec. 5;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_pi (k : ℕ) : ∀ (A : Fin k → Type u) [∀ j, Ring (A j)],
    (∀ j, LVH2GL3.StableK2Trivial (A j)) → LVH2GL3.StableK2Trivial ((j : Fin k) → A j) := by
  induction k with
  | zero =>
      intro A _ _
      haveI : Subsingleton ((j : Fin 0) → A j) := ⟨fun f g => funext fun j => j.elim0⟩
      exact stableK2Trivial_of_subsingleton
  | succ k ih =>
      intro A _ hA
      exact stableK2Trivial_of_ringEquiv (piFinSuccRingEquiv k A).symm
        (stableK2Trivial_prod (hA 0) (ih (fun j => A j.succ) (fun j => hA j.succ)))

/-- Finite products of matrix rings over `F` have trivial stable `K₂` when `F` does.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_matrixPi {F : Type u} [Ring F] (hF : LVH2GL3.StableK2Trivial F)
    (k : ℕ) (d : Fin (k + 1) → ℕ) :
    LVH2GL3.StableK2Trivial ((j : Fin (k + 1)) → Matrix (Fin (d j)) (Fin (d j)) F) :=
  stableK2Trivial_pi (k + 1) (fun j => Matrix (Fin (d j)) (Fin (d j)) F)
    (fun j => stableK2Trivial_matrix (d j) hF)

/-- **Ultramatricial `𝔽₂`-rings have trivial stable `K₂`**, given stable `K₂(𝔽₂) = 0`
(Ara–Brustenga–Cortiñas 2009, Sec. 5; `simple_kazhdan_sofic_group.tex` l.733-735,
`sec:questions`, leaf T1b.iii.) -/
theorem stableK2Trivial_of_isUltramatricialF2 {S : Type*} [Ring S]
    (h2 : LVH2GL3.StableK2Trivial (ZMod 2)) (hS : LVSkewLaurentK2.IsUltramatricialF2 S) :
    LVH2GL3.StableK2Trivial S := by
  refine stableK2Trivial_of_subrings ?_
  intro s
  obtain ⟨k, d, T, hsT, ⟨e⟩⟩ := hS s
  exact ⟨T, hsT, stableK2Trivial_of_ringEquiv e.symm (stableK2Trivial_matrixPi h2 k d)⟩

end GroupApproximation.Full.LVCohnK2
