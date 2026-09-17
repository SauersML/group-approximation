import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SpatialInvolutions
import GroupApproximation.Meta.AxiomGuard

/-!
# Local non-metabelianity of `[[T]]`, part 1: upstream interfaces

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no tex line).  Infrastructure lane `sk-flip-05`.

The non-metabelian witness of `InfraNonMetab` uses two results of parallel lanes that are not yet
on disk.  They are stated here as `Statement`s, with exactly the lane shapes, so that each is
discharged by `fun X .. => <lane theorem> ..` once it lands.

* `TowerBaseStatement` (lane `sk-flip-03`, `exists_isClopen_tower`): for an aperiodic
  homeomorphism `T` of a compact Hausdorff totally disconnected space, a nonempty open `W` and
  `n : ℕ`, there is a nonempty clopen `V` with `T^i V ⊆ W` for `i < n` and the levels `T^i V`
  (`i < n`) pairwise disjoint.
  TRUE: pick `x ∈ W`.  By aperiodicity the points `T^i x` (`i < n`) are pairwise distinct, so
  they have pairwise disjoint open neighbourhoods `O_i` (Hausdorff, finitely many pairs).  The
  open set `⋂_{i<n} T^{-i}(O_i ∩ W)` contains `x`, hence contains a clopen neighbourhood `V` of
  `x` (clopen basis); then `T^i V ⊆ O_i ∩ W`, and the `O_i` are disjoint.
* `TowerPermEmbeddingStatement` (lane `sk-flip-04`, `towerPerm`): if `V` is a nonempty clopen set
  whose levels `T^i V` (`i < n`) are pairwise disjoint, there is an injective homomorphism
  `S_n →* [[T]]` whose image is supported in the tower `⋃_i T^i V`.
  TRUE (no further hypothesis on `X` or `T`): for `σ ∈ S_n` let `φ σ` act by `T^{σ i - i}` on
  the level `T^i V` and by the identity off the tower.  The levels are clopen and pairwise
  disjoint, so the cocycle (`σ i - i` on level `i`, `0` off the tower) is continuous (constant on
  each piece of a finite clopen partition); `φ σ` maps level `i` onto level `σ i`, so it is a
  bijection with inverse `φ σ⁻¹`, and continuity of both gives a homeomorphism in `[[T]]`.
  On level `i`, `φ σ (φ τ x) = T^{σ (τ i) - τ i} T^{τ i - i} x = φ (σ τ) x`, so `φ` is a
  homomorphism.  If `φ σ = 1` and `v ∈ V` then `T^{σ i} v = T^i v` lies in the levels `σ i` and
  `i`, which are disjoint unless `σ i = i`; hence `σ = 1`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

universe u

/-- Lane `sk-flip-03` interface: a clopen tower base with `n` pairwise disjoint levels inside a
nonempty open set (see the module docstring for why it is true). -/
def TowerBaseStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (T : X ≃ₜ X), IsAperiodic T → ∀ W : Set X, IsOpen W → W.Nonempty → ∀ n : ℕ,
      ∃ V : Set X, IsClopen V ∧ V.Nonempty ∧ (∀ i < n, (T ^ (i : ℤ)) '' V ⊆ W) ∧
        ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V)

/-- Lane `sk-flip-04` interface: permutations of the levels of a clopen tower embed `S_n` into
`[[T]]`, supported in the tower (see the module docstring for why it is true). -/
def TowerPermEmbeddingStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (T : X ≃ₜ X) (V : Set X) (n : ℕ), IsClopen V →
    V.Nonempty →
      (∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V)) →
        ∃ φ : Equiv.Perm (Fin n) →* topologicalFullGroup T, Function.Injective φ ∧
          ∀ σ : Equiv.Perm (Fin n),
            SupportedIn (φ σ : X ≃ₜ X) (⋃ i : Fin n, (T ^ ((i : ℕ) : ℤ)) '' V)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.TowerBaseStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.TowerPermEmbeddingStatement
