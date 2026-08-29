import GroupApproximation.Sofic.WeakMFUltraproduct

/-!
# Operator-norm almost representations without separation

Cutting a weak-MF approximation by a central spectral projection preserves
unitarity and asymptotic multiplicativity, but it need not preserve the fixed
separation estimate for arbitrary group elements.  This file isolates the
weaker structure consumed by the Kazhdan-compressor argument.

`WeakMFApproximation.toOpAlmostRepresentation` forgets only the separation
fields.  No new approximation notion is introduced at the group level.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-- A sequential family of finite-dimensional unitary maps whose
multiplicative defect tends to zero in operator norm. -/
structure OpAlmostRepresentation (G : Type u) [Group G] where
  model : ℕ → FiniteModel
  modelNonempty : ∀ n, 0 < Fintype.card (model n)
  map : ∀ n, G → Matrix.unitaryGroup (model n) ℂ
  asymptoticallyMultiplicative : ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    ‖(map n (g * h) : Matrix (model n) (model n) ℂ) -
        (map n g : Matrix (model n) (model n) ℂ) * map n h‖ ≤ ε

namespace OpAlmostRepresentation

/-- Restrict an operator-norm almost representation along a homomorphism. -/
abbrev comap {H : Type*} [Group H] (A : OpAlmostRepresentation G)
    (iota : H →* G) : OpAlmostRepresentation H where
  model := A.model
  modelNonempty := A.modelNonempty
  map n h := A.map n (iota h)
  asymptoticallyMultiplicative g h ε hε := by
    simpa only [map_mul] using
      A.asymptoticallyMultiplicative (iota g) (iota h) ε hε

/-- Reindex an operator-norm almost representation along a pointwise cofinal
map.  The inequality `n ≤ φ n` preserves all eventual operator-norm
estimates, exactly as for `WeakMFApproximation.reindex`. -/
def reindex (A : OpAlmostRepresentation G) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) : OpAlmostRepresentation G where
  model n := A.model (φ n)
  modelNonempty n := A.modelNonempty (φ n)
  map n := A.map (φ n)
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h ε hε
    exact ⟨N, fun n hn ↦ hN (φ n) (hn.trans (hφ n))⟩

end OpAlmostRepresentation

end GroupApproximation
