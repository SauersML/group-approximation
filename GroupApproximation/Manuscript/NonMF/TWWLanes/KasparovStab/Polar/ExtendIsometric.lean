import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Polar unitary, lane `nm-tww-17b`: the isometric extension

Step 3 of Lance, Thm. 3.5. Let `S : E → E'` and `T : E → G` be adjointable, with
`⟨Tx, Tx⟩ = ⟨Sx, Sx⟩` for every `x`. Suppose `S` has dense range and `G` is complete. Then the
map `Sx ↦ Tx` extends to a map `W : E' → G` with

  `‖T x - W u‖ ≤ ‖S x - u‖` for all `u`, `x`.

The inequality holds because `W` is the isometric extension and `W (S x) = T x`. We keep only
this inequality. It pins `W` down on the dense set (`u = S x` gives `W (S x) = T x`), and it
is all the adjoint relation and the inverse identities of `Polar/ExtendAdjoint.lean` need.
Linearity of `W` is never proved directly. It follows once `W` is adjointable.

Route.
* `‖T x - T y‖ = ‖S x - S y‖`, from the diagonal identity applied to `x - y`
  (`Adjointable.map_sub`).
* For each `u`, choose `x u n` with `S (x u n) → u` (`exists_seq_isLimit`). Then
  `T (x u n)` is Cauchy, and `W u` is its limit in the complete module `G`.
* For fixed `x` and `ε`, pick `k` late enough. Then
  `‖T x - W u‖ ≤ ‖S x - S (x u k)‖ + ‖T (x u k) - W u‖
    ≤ ‖S x - u‖ + ‖S (x u k) - u‖ + ε/2 ≤ ‖S x - u‖ + ε`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

open GroupApproximation.HilbertModule

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **A point of the closure of a range is a limit of a sequence from the range.** -/
theorem exists_seq_isLimit {E F : CStarModule.{v, v} B} (S : Adjointable E F) {u : F.carrier}
    (hu : IsApprox S u) : ∃ x : ℕ → E.carrier, IsLimit F (fun n => S.toFun (x n)) u := by
  choose x hx using fun n : ℕ => hu (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  refine ⟨x, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  calc F.norm (S.toFun (x n) - u) ≤ 1 / ((n : ℝ) + 1) := hx n
    _ ≤ 1 / ((N : ℝ) + 1) := Nat.one_div_le_one_div hn
    _ ≤ ε := hN.le

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.exists_seq_isLimit

/-- **Isometric extension** (Lance, Thm. 3.5, step 3). If `⟨Tx, Tx⟩ = ⟨Sx, Sx⟩`, `S` has dense
range and `G` is complete, then there is `W` with `‖T x - W u‖ ≤ ‖S x - u‖`. -/
theorem exists_isometricExtension {E E' G : CStarModule.{v, v} B} (S : Adjointable E E')
    (T : Adjointable E G)
    (hST : ∀ x : E.carrier,
      G.inner (T.toFun x) (T.toFun x) = E'.inner (S.toFun x) (S.toFun x))
    (hS : HasDenseRange S) (hG : IsCompleteModule G) :
    ∃ W : E'.carrier → G.carrier, ∀ (u : E'.carrier) (x : E.carrier),
      G.norm (T.toFun x - W u) ≤ E'.norm (S.toFun x - u) := by
  have hnorm : ∀ x y : E.carrier,
      G.norm (T.toFun x - T.toFun y) = E'.norm (S.toFun x - S.toFun y) := by
    intro x y
    rw [← T.map_sub, ← S.map_sub, CStarModule.norm_def, CStarModule.norm_def, hST]
  choose x hx using fun u : E'.carrier => exists_seq_isLimit S (hS u)
  have hc : ∀ u : E'.carrier, IsCauchy G fun n => T.toFun (x u n) := by
    intro u ε hε
    obtain ⟨N, hN⟩ := hx u (ε / 2) (half_pos hε)
    refine ⟨N, fun m n hm hn => ?_⟩
    have hm' : E'.norm (S.toFun (x u m) - u) ≤ ε / 2 := hN m hm
    have hn' : E'.norm (S.toFun (x u n) - u) ≤ ε / 2 := hN n hn
    show G.norm (T.toFun (x u m) - T.toFun (x u n)) ≤ ε
    rw [hnorm]
    calc E'.norm (S.toFun (x u m) - S.toFun (x u n))
        ≤ E'.norm (S.toFun (x u m) - u) + E'.norm (u - S.toFun (x u n)) :=
          modNorm_sub_le E' _ _ _
      _ = E'.norm (S.toFun (x u m) - u) + E'.norm (S.toFun (x u n) - u) := by
          rw [modNorm_sub_comm E' u (S.toFun (x u n))]
      _ ≤ ε / 2 + ε / 2 := add_le_add hm' hn'
      _ = ε := add_halves ε
  choose W hW using fun u : E'.carrier => hG _ (hc u)
  refine ⟨W, fun u y => le_of_forall_pos_le_add fun ε hε => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hW u (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hx u (ε / 2) (half_pos hε)
  have h1 : G.norm (T.toFun (x u (max N₁ N₂)) - W u) ≤ ε / 2 := hN₁ _ (le_max_left _ _)
  have h2 : E'.norm (S.toFun (x u (max N₁ N₂)) - u) ≤ ε / 2 := hN₂ _ (le_max_right _ _)
  have h3 : G.norm (T.toFun y - W u) ≤
      G.norm (T.toFun y - T.toFun (x u (max N₁ N₂)))
        + G.norm (T.toFun (x u (max N₁ N₂)) - W u) :=
    modNorm_sub_le G _ _ _
  have h4 : E'.norm (S.toFun y - S.toFun (x u (max N₁ N₂))) ≤
      E'.norm (S.toFun y - u) + E'.norm (u - S.toFun (x u (max N₁ N₂))) :=
    modNorm_sub_le E' _ _ _
  rw [hnorm] at h3
  rw [modNorm_sub_comm E' u (S.toFun (x u (max N₁ N₂)))] at h4
  linarith

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.exists_isometricExtension

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab
