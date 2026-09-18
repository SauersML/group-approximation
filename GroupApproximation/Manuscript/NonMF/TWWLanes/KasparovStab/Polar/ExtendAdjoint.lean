import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.ExtendIsometric
import GroupApproximation.Meta.AxiomGuard

/-!
# Polar unitary, lane `nm-tww-17b`: the extensions are mutually adjoint and inverse

Steps 4 and 5 of Lance, Thm. 3.5. Let `S : E → E'` and `T : E → G` be adjointable with
`⟨Tx, Ty⟩ = ⟨Sx, Sy⟩` and both of dense range. Suppose `W : E' → G` and `V : G → E'` satisfy
the extension inequalities of `Polar/ExtendIsometric.lean`:

  `‖T x - W u‖ ≤ ‖S x - u‖`,  `‖S x - V v‖ ≤ ‖T x - v‖`.

Then `⟨W u, v⟩ = ⟨u, V v⟩` (`isometricExtension_inner`) and `V (W u) = u`
(`isometricExtension_leftInverse`). Applying the second with the roles swapped gives
`W (V v) = v`. So `W` is an adjointable unitary with adjoint `V`. This replaces the route
"range W is closed and dense": surjectivity comes from the second extension `V`.

Route for the inner product. Only continuity in the second slot is used
(`IsLimit.tendsto_inner_right`).
* `⟨T y, W u⟩ = ⟨S y, u⟩`: take `S (x n) → u`. Then `T (x n) → W u`, and the two sequences
  `⟨T y, T (x n)⟩ = ⟨S y, S (x n)⟩` agree. Conjugate symmetry gives `⟨W u, T y⟩ = ⟨u, S y⟩`.
* `⟨W u, v⟩ = ⟨u, V v⟩`: take `T (y n) → v`. Then `S (y n) → V v`, and
  `⟨W u, T (y n)⟩ = ⟨u, S (y n)⟩`.

Route for the inverse. Pick `x` with `‖S x - u‖ ≤ ε/2`. Then
`‖V (W u) - u‖ ≤ ‖S x - V (W u)‖ + ‖S x - u‖ ≤ ‖T x - W u‖ + ε/2 ≤ ‖S x - u‖ + ε/2 ≤ ε`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

open GroupApproximation.HilbertModule Filter Topology

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **The two extensions are adjoint**: `⟨W u, v⟩ = ⟨u, V v⟩`. -/
theorem isometricExtension_inner {E E' G : CStarModule.{v, v} B} (S : Adjointable E E')
    (T : Adjointable E G) {W : E'.carrier → G.carrier} {V : G.carrier → E'.carrier}
    (hW : ∀ (u : E'.carrier) (x : E.carrier),
      G.norm (T.toFun x - W u) ≤ E'.norm (S.toFun x - u))
    (hV : ∀ (v : G.carrier) (x : E.carrier),
      E'.norm (S.toFun x - V v) ≤ G.norm (T.toFun x - v))
    (hinner : ∀ x y : E.carrier,
      G.inner (T.toFun x) (T.toFun y) = E'.inner (S.toFun x) (S.toFun y))
    (hS : HasDenseRange S) (hT : HasDenseRange T) (u : E'.carrier) (v : G.carrier) :
    G.inner (W u) v = E'.inner u (V v) := by
  have hA' : ∀ (y : E.carrier) (w : E'.carrier),
      G.inner (T.toFun y) (W w) = E'.inner (S.toFun y) w := by
    intro y w
    obtain ⟨x, hx⟩ := exists_seq_isLimit S (hS w)
    have hTx : IsLimit G (fun n => T.toFun (x n)) (W w) := by
      intro ε hε
      obtain ⟨N, hN⟩ := hx ε hε
      exact ⟨N, fun n hn => le_trans (hW w (x n)) (hN n hn)⟩
    have h1 := hTx.tendsto_inner_right (T.toFun y)
    have h2 := hx.tendsto_inner_right (S.toFun y)
    exact tendsto_nhds_unique (h1.congr fun n => hinner y (x n)) h2
  have hA : ∀ (w : E'.carrier) (y : E.carrier),
      G.inner (W w) (T.toFun y) = E'.inner w (S.toFun y) := by
    intro w y
    have h := congrArg star (hA' y w)
    rwa [G.inner_star, E'.inner_star] at h
  obtain ⟨y, hy⟩ := exists_seq_isLimit T (hT v)
  have hSy : IsLimit E' (fun n => S.toFun (y n)) (V v) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hy ε hε
    exact ⟨N, fun n hn => le_trans (hV v (y n)) (hN n hn)⟩
  have h1 := hy.tendsto_inner_right (W u)
  have h2 := hSy.tendsto_inner_right u
  exact tendsto_nhds_unique (h1.congr fun n => hA u (y n)) h2

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isometricExtension_inner

/-- **The extensions are inverse**: `V (W u) = u`. -/
theorem isometricExtension_leftInverse {E E' G : CStarModule.{v, v} B} (S : Adjointable E E')
    (T : Adjointable E G) {W : E'.carrier → G.carrier} {V : G.carrier → E'.carrier}
    (hW : ∀ (u : E'.carrier) (x : E.carrier),
      G.norm (T.toFun x - W u) ≤ E'.norm (S.toFun x - u))
    (hV : ∀ (v : G.carrier) (x : E.carrier),
      E'.norm (S.toFun x - V v) ≤ G.norm (T.toFun x - v))
    (hS : HasDenseRange S) (u : E'.carrier) : V (W u) = u := by
  refine eq_of_norm_sub_le E' fun ε hε => ?_
  obtain ⟨x, hx⟩ := hS u (ε / 2) (half_pos hε)
  have hx' : E'.norm (S.toFun x - u) ≤ ε / 2 := hx
  calc E'.norm (V (W u) - u)
      ≤ E'.norm (V (W u) - S.toFun x) + E'.norm (S.toFun x - u) := modNorm_sub_le E' _ _ _
    _ = E'.norm (S.toFun x - V (W u)) + E'.norm (S.toFun x - u) := by
      rw [modNorm_sub_comm E' (V (W u)) (S.toFun x)]
    _ ≤ G.norm (T.toFun x - W u) + E'.norm (S.toFun x - u) :=
      add_le_add (hV (W u) x) le_rfl
    _ ≤ E'.norm (S.toFun x - u) + E'.norm (S.toFun x - u) := add_le_add (hW u x) le_rfl
    _ ≤ ε / 2 + ε / 2 := add_le_add hx' hx'
    _ = ε := add_halves ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isometricExtension_leftInverse

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab
