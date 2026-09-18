import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.SchreierSwap
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive

/-!
# Stable `K₂(𝔽₂) = 0`

For `N ≥ 3` the projection `St_N(𝔽₂) → E_N(𝔽₂)` is injective. By induction on `A`, the block
`Blk A` acts faithfully on `(e_l)_{l ∈ A}`. In the step `A = insert p B`, the Schreier argument
puts the stabilizer of `e_p` into `Hp p A`, and `stab_step` finishes. Taking `A = univ` gives
injectivity, and stable triviality of `K₂(𝔽₂)` follows with `N = n + 3` (Steinberg 1962; Milnor,
*Introduction to algebraic K-theory*, §9-10). This proves `simple_kazhdan_sofic_group.tex`
l.733-735 (leaf T1b.iii) for `𝔽₂`.
-/

namespace GroupApproximation.Full.LVFieldK2

open SteinbergGroup

variable {N : ℕ}

/-- Every Schreier generator for the orbit of `e_p` under `Blk A` lies in `Hp p A`. -/
theorem schreier_step (hN : 3 ≤ N) {p : Fin N} {A : Finset (Fin N)} (hp : p ∈ A) :
    ∀ s ∈ rootGens (fun i j => i ∈ A ∧ j ∈ A), ∀ v, ∀ t ∈ Trans p A v,
      ∃ t' ∈ Trans p A (act s v), t'⁻¹ * (s * t) ∈ Hp p A := by
  rintro s ⟨i, j, h, ⟨hi, hj⟩, rfl⟩ v t ⟨q, hq, hq1, y, hy, hyv, rfl⟩
  by_cases hjq : j = q
  · subst hjq
    exact step_case2 hq h hi hq1 hy hyv
  by_cases hiq : i = q
  · subst hiq
    rcases zmodTwo_eq_zero_or_one (v j) with hvj | hvj
    · exact step_case3a hN hp hq h hj hq1 hvj hy hyv
    · exact step_case3b hN hp hq h hj hvj hy hyv
  exact step_case1 hN hp hq h hi hj hiq hjq hq1 hy hyv

/-- `Blk A` acts faithfully on the basis vectors `(e_l)_{l ∈ A}`. -/
theorem Blk_faithful (hN : 3 ≤ N) (A : Finset (Fin N)) :
    ∀ g ∈ Blk A, (∀ l ∈ A, act g (e l) = e l) → g = 1 := by
  induction A using Finset.induction_on with
  | empty =>
    intro g hg _
    have hle : Blk (∅ : Finset (Fin N)) ≤ ⊥ :=
      rootSub_le (Φ := fun i j => i ∈ (∅ : Finset (Fin N)) ∧ j ∈ (∅ : Finset (Fin N)))
        fun i _ _ hΦ => absurd hΦ.1 (Finset.notMem_empty i)
    exact Subgroup.mem_bot.mp (hle hg)
  | insert p B hpB ih =>
    intro g hg hfix
    have hp : p ∈ insert p B := Finset.mem_insert_self p B
    have hgH : g ∈ Hp p (insert p B) :=
      schreier (S := rootGens (fun i j => i ∈ insert p B ∧ j ∈ insert p B)) rootGens_inv
        act act_one act_mul (Trans p (insert p B)) (Hp p (insert p B))
        (schreier_step hN hp) (e p) (Trans_base p _) (one_mem_Trans hp) g hg (hfix p hp)
    exact stab_step hpB ih g hgH hfix

/-- The root elements `x_{ij}(1)` generate `St_N(𝔽₂)`. -/
theorem Blk_univ : Blk (Finset.univ : Finset (Fin N)) = ⊤ := by
  have hgen := PresentedGroup.closure_range_of (SteinbergGroup.relations (I := Fin N)
    (R := ZMod 2))
  refine eq_top_iff.mpr (hgen.symm.le.trans (Subgroup.closure_le.mpr ?_))
  rintro _ ⟨⟨i, j, hij, a⟩, rfl⟩
  change x (R := ZMod 2) i j hij a ∈ Blk Finset.univ
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl
  · rw [x_zero]
    exact (Blk _).one_mem
  · exact X_mem_Blk i j hij (Finset.mem_univ i) (Finset.mem_univ j)

/-- For `N ≥ 3`, `K₂(N, 𝔽₂) = ker (St_N(𝔽₂) → E_N(𝔽₂))` is trivial. -/
theorem projection_injective_zmodTwo (hN : 3 ≤ N) (g : St N) (hg : projection g = 1) :
    g = 1 :=
  Blk_faithful hN Finset.univ g (by rw [Blk_univ]; exact Subgroup.mem_top g)
    fun l _ => act_eq_self_of_projection hg (e l)

/-- **Stable `K₂(𝔽₂) = 0`** (Steinberg 1962; Milnor §9-10): every element of `K₂(n, 𝔽₂)`
dies in `St_{n+3}(𝔽₂)`. -/
theorem stableK2Trivial_zmodTwo : GroupApproximation.Full.LVH2GL3.StableK2Trivial (ZMod 2) := by
  intro n k hk
  refine ⟨n + 3, Nat.le_add_right n 3, ?_⟩
  exact projection_injective_zmodTwo (N := n + 3) (by omega) _
    (LVH2GL3.projection_indexMap_eq_one _ hk)

end GroupApproximation.Full.LVFieldK2
