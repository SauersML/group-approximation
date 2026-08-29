import GroupApproximation.GGT.DGOIsolatedComponentSideForm
import GroupApproximation.GGT.DGOIsolatedComponentBoundFourGon

/-!
# The §4.2 bound for a 4-gon, with the component anywhere it can already be put

`DGOIsolatedComponentBoundFourGon.span_mem_relBall_of_sideZero` is Dahmani--
Guirardel--Osin's Lemma 4.16 composed with their Lemma 4.6, at `(μ,b) = (1,0)`,
`n = 4`, with the distinguished component as the side `0`.  This module is the
adapter between that and the transfers of `DGOIsolatedComponentSideForm` and
`…Straddle`, and the two theorems those transfers already close with it:

* `span_mem_relBall_of_isSide` --- the component IS a side, at any index `t < 4`.
  The rotation does the work; there is no recut and no collapse.
* `span_mem_relBall_of_straddle_two` --- the component straddles two corners.
  The recut then yields exactly four sides, so the same base case applies.

Both land at `25 (δ+1) · 4 = 100 (δ+1)`, which is dgo-cycle's constant.

What is NOT here is the case of a component interior to a side, or straddling a
single corner: those recut to six and five sides respectively, and the base case
is proved at four.  They are the general-position case, and they need either a
base case stated with the component at an interior index of side `0` --- which
keeps the polygon a quadrilateral, since at `(1,0)` a component inside a geodesic
side is a single letter (`isComp_eq_succ_of_geodesic`) --- or the side count
raised.  That decision is not this module's.

## The adapter, and why it is a theorem rather than a term

`baseCase_of_sideZero_at` restates their theorem in the binder shape
`sideForm_of_baseCase` takes: `lam` before the clause rather than after it, the
constant as `C * N` with `C = 25 (δ+1)` rather than as `100 (δ+1)`, and the side
count as a variable `N` carrying `N = 4` rather than the literal.  The variable is
what lets the recut instantiate it: the recut's count is `n + 2 - (t' - t)`, which
is `4` when the component straddles two corners but is not the literal `4`, and
`subst` on `hN` is what makes those meet.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The adapter -/

/-- **dgo-cycle's base case, in the shape the transfers take.**

Their `span_mem_relBall_of_sideZero` with `lam` moved before the clause, the
constant written `25 (δ+1) * N`, and the side count carried as a variable equal
to `4`. -/
theorem baseCase_of_sideZero_at (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) {N : ℕ}
    (hN : N = 4) :
    ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / 1 - 0
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1)
          ∈ D.relBall lam (25 * (δ + 1) * N) := by
  subst hN
  intro v w c hlet hclosed hc0 hc4 hcmono lam hcqg hcomp hiso
  rw [show 25 * (δ + 1) * 4 = 100 * (δ + 1) from by ring]
  exact span_mem_relBall_of_sideZero D hsymm hδ v w c hlet hclosed hc0 hc4 hcmono
    hcqg lam hcomp hiso

/-! ## The component is a side -/

/-- **The bound for a component that is a side of a `(1,0)`-quasi-geodesic 4-gon,
at any index.**

The base case has it at the side `0`; `sideForm_of_baseCase` rotates the polygon
so that any side `t` becomes the first.  Nothing else changes: the span is the
same group element, and the clause is asked of `s ≠ t` before and of `s ≠ 0`
after. -/
theorem span_mem_relBall_of_isSide (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) (hlet : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) (hc0 : c 0 = 0) (hc4 : c 4 = w.length)
    (hcmono : ∀ s : ℕ, c s ≤ c (s + 1)) (lam : Λ) (t : ℕ) (ht : t < 4)
    (hcqg : ∀ s : ℕ, s < 4 → s ≠ t → ∀ p q : ℕ, c s ≤ p → p ≤ q →
      q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    (hcomp : IsComp lam w (c t) (c (t + 1)))
    (hiso : IsIsolated D.fam lam v w (c t)) :
    (vertex v w (c t))⁻¹ * vertex v w (c (t + 1))
      ∈ D.relBall lam (25 * (δ + 1) * 4) :=
  sideForm_of_baseCase D 1 0 (25 * (δ + 1))
    (baseCase_of_sideZero_at D hsymm hδ rfl) v w c hlet hclosed hc0 hc4 hcmono
    lam t ht hcqg hcomp hiso

/-! ## The component straddles two corners -/

/-- **The bound for a component straddling two corners of a
`(1,0)`-quasi-geodesic 4-gon.**

The recut makes it a side of a polygon with `4 + 2 - (t' - t) = 4` sides, so the
same base case applies.  This is the one straddling case that needs no side count
beyond four, and at `(1,0)` such a run has at most three letters --- one on each
side it meets. -/
theorem span_mem_relBall_of_straddle_two (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {lam : Λ} {i k t t' : ℕ}
    (ht : t < 4) (hti : c t ≤ i) (hit : i ≤ c (t + 1)) (ht' : t' < 4)
    (htk : c t' ≤ k) (hkt' : k ≤ c (t' + 1)) (htt2 : t' = t + 2)
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hc4 : c 4 = w.length) (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (hcqg : ∀ s : ℕ, s < 4 → ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
      ((q - p : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    (hcomp : IsComp lam w i k) (hiso : IsIsolated D.fam lam v w i) :
    (vertex v w i)⁻¹ * vertex v w k ∈ D.relBall lam (25 * (δ + 1) * 4) := by
  have hN : 4 + 2 - (t' - t) = 4 := by omega
  have h := isolatedComponent_span_of_baseCase D 1 0 (25 * (δ + 1)) ht hti hit
    ht' htk hkt' (by omega) (baseCase_of_sideZero_at D hsymm hδ hN) hlet hclosed
    hc0 hc4 hcmono hcqg hcomp hiso
  rwa [hN] at h

end OsinComponents
end GGT
end GroupApproximation
