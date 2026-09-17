import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SpatialInvolutions
import GroupApproximation.Meta.AxiomGuard

/-!
# Local non-metabelianity of `[[T]]`, part 1: the tower-permutation interface

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no tex line).  Infrastructure lane `sk-flip-05`.

The lane plan used two upstream interfaces.

* Lane `sk-flip-03` (tower base).  The consecutive-levels shape `T^i V ⊆ W` (`i < n`) is FALSE
  for `n ≥ 2` whenever `W ∩ T W = ∅` (`not_exists_tower_of_disjoint_image`, `InfraTowerBase`).
  The corrected, proved form is on disk: `exists_isClopen_tower_in_open` (`InfraTowerBaseMinimal`)
  gives a nonempty clopen `V` and injective exponents `k : Fin n → ℤ` with the levels `T^{k i} V`
  inside `W` and pairwise disjoint.  It is imported and used directly by `InfraNonMetab`.
* Lane `sk-flip-04` (tower permutations) is not yet on disk.  Because the levels delivered by
  lane 03 sit at arbitrary exponents, the interface is stated for levels `T^{k i} V` (the lane-04
  shape is the special case `k i = i`).  `TowerPermEmbeddingStatement`: if `V` is a nonempty
  clopen set whose levels `T^{k i} V` (`i : Fin n`) are pairwise disjoint, there is an injective
  homomorphism `S_n →* [[T]]` supported in `⋃_i T^{k i} V`.

`TowerPermEmbeddingStatement` is TRUE (no hypothesis on `X` or `T` beyond the printed ones): for
`σ ∈ S_n` let `φ σ` act by `T^{k (σ i) - k i}` on the level `T^{k i} V` and by the identity off
the tower.  The levels are clopen and pairwise disjoint, so the cocycle (`k (σ i) - k i` on level
`i`, `0` off the tower) is continuous (constant on each piece of a finite clopen partition).
`φ σ` maps level `i` onto level `σ i`, so it is a bijection with inverse `φ σ⁻¹`; both are
continuous, so `φ σ ∈ [[T]]`.  On level `i`,
`φ σ (φ τ x) = T^{k (σ (τ i)) - k (τ i)} T^{k (τ i) - k i} x = φ (σ τ) x`, so `φ` is a
homomorphism.  If `φ σ = 1` and `v ∈ V` then `T^{k (σ i)} v = T^{k i} v` lies in the levels
`σ i` and `i`, which are disjoint unless `σ i = i`; hence `σ = 1`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

universe u

/-- Lane `sk-flip-04` interface (levels at arbitrary exponents): permuting the levels of a clopen
tower embeds `S_n` into `[[T]]` with support in the tower (see the module docstring for why it is
true). -/
def TowerPermEmbeddingStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (T : X ≃ₜ X) (V : Set X) (n : ℕ) (k : Fin n → ℤ),
    IsClopen V → V.Nonempty →
      (∀ i j, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V)) →
        ∃ φ : Equiv.Perm (Fin n) →* topologicalFullGroup T, Function.Injective φ ∧
          ∀ σ : Equiv.Perm (Fin n), SupportedIn (φ σ : X ≃ₜ X) (⋃ i : Fin n, (T ^ k i) '' V)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.TowerPermEmbeddingStatement
