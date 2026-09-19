import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.WPDHyperbolicallyEmbedded

/-!
# From hyperbolicity of `Γ(G,A)` back to the four-point condition on `A`

`CayleyFourPointBridge.isHyperbolicSpace_cayley_of_fourPoint` goes one way: a
`δ`-four-point alphabet makes `Cayley A` a `δ`-hyperbolic space.  This module is
the converse, which is what Dahmani--Guirardel--Osin's §4.2 needs, because their
Definition 4.25 hands hyperbolicity over in the *space* form and every estimate
of §4.2 consumes it in the `ℕ`-valued *alphabet* form.

## Why this is a change of variables and a cast, not geometry

`HullGeometry.IsHyperbolicSpace δ X` is

    ∀ w x y z, min (gromovProduct x y w) (gromovProduct y z w) - δ
      ≤ gromovProduct x z w ,

with `gromovProduct x y w = (d(x,w) + d(y,w) - d(x,y)) / 2`, and
`Hyperbolic.isFourPointHyperbolic_iff_gromovProduct` already rearranges
`IsFourPointHyperbolic` into the same shape over `ℤ`, at twice the products.  So
the two differ by a transposition of two of the four points, a factor of two and
the passage from `ℝ` to `ℕ`.  Nothing here needs slim triangles: routing through
`isFourPointHyperbolic_of_isSlimTriangles` would be a detour that loses
constants for a statement that is already a four-point condition.

The transposition is done inside
`isFourPointHyperbolic_of_isHyperbolicSpace_cayley`, by instantiating the space
form at `(q, r, p, s)` when the alphabet form is being proved at `(p, q, r, s)`;
`fourPoint_of_min_gromov` is kept symmetric in its six distances --- the exact
mirror of the landed `min_gromov_le_of_fourPoint` --- so that it is reusable
whatever convention a caller has.

## The constant

`⌈δ⌉₊`.  `Nat.le_ceil` holds for every real, negative ones included, where the
ceiling is `0`; no positivity hypothesis on `δ` is needed, and none is available
from Definition 4.25, whose clause (a) binds `δ : ℝ` existentially with no sign
condition.

## What it closes

`exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded` derives the `hδ`
binder of the §4.2 chain from `IsHyperbolicallyEmbedded` alone --- for a
`HypEmbeddedCore₂ A N` that is `E.embedded`, with no appeal to suitability, to
the loxodromic pair, or to anything else the core carries, and with no transport:
`E.rel.alphabet` is literally the `Cayley` argument of clause (a).
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## 1.  The arithmetic -/

/-- **The min form implies the max form**, at six reals and with no constant
lost --- the exact mirror of `min_gromov_le_of_fourPoint`.

The min splits into two cases and each is one `linarith`: if the first product
is the smaller then `dwy + dxz ≤ dwz + dxy + 2e`, and if the second is then
`dwy + dxz ≤ dwx + dyz + 2e`; either bound is at most the maximum.

Stated on bare reals, with no metric and no convention, so that a caller may
instantiate it at whichever transposition of the four points its own Gromov
product uses. -/
theorem fourPoint_of_min_gromov {dwx dwy dwz dxy dyz dxz e : ℝ}
    (h : min ((dwx + dwy - dxy) / 2) ((dwy + dwz - dyz) / 2) - e
      ≤ (dwx + dwz - dxz) / 2) :
    dwy + dxz ≤ max (dwx + dyz) (dwz + dxy) + 2 * e := by
  rcases le_total ((dwx + dwy - dxy) / 2) ((dwy + dwz - dyz) / 2) with hle | hle
  · rw [min_eq_left hle] at h
    have hmax := le_max_right (dwx + dyz) (dwz + dxy)
    linarith
  · rw [min_eq_right hle] at h
    have hmax := le_max_left (dwx + dyz) (dwz + dxy)
    linarith

/-! ## 2.  The cast -/

/-- **A `δ`-hyperbolic `Γ(G,A)` makes `A` a `⌈δ⌉₊`-four-point alphabet.**

The space form is instantiated at `(q, r, p, s)` --- that transposition is what
turns its distinguished product into the one the alphabet form concludes about
--- and then `fourPoint_of_min_gromov` is applied at the six word distances.
The remaining work is bookkeeping, in the style of the converse bridge: each
`dist` is named as a cast of a `wordDist` before `gromovProduct` is unfolded,
`Nat.le_ceil` absorbs `δ`, and the symmetry of the word metric matches the two
sides of the maximum.

The maximum is split in `ℝ` rather than compared with the `ℕ` one, so no
`Nat.cast_max` rewriting is needed and each branch ends with `omega` against
`le_max_left` / `le_max_right`. -/
theorem isFourPointHyperbolic_of_isHyperbolicSpace_cayley {G : Type u} [Group G]
    (A : Alphabet G) {δ : ℝ} (h : IsHyperbolicSpace δ (Cayley A)) :
    Hyperbolic.IsFourPointHyperbolic A.carrier ⌈δ⌉₊ := by
  intro p q r s
  have hS := A.symmetricGenerating
  have hcel : δ ≤ (⌈δ⌉₊ : ℝ) := Nat.le_ceil δ
  have key := h (Cayley.of A q) (Cayley.of A r) (Cayley.of A p) (Cayley.of A s)
  have hrq : dist (Cayley.of A r) (Cayley.of A q)
      = ((wordDist A.carrier r q : ℕ) : ℝ) := Cayley.dist_eq _ _
  have hpq : dist (Cayley.of A p) (Cayley.of A q)
      = ((wordDist A.carrier p q : ℕ) : ℝ) := Cayley.dist_eq _ _
  have hrp : dist (Cayley.of A r) (Cayley.of A p)
      = ((wordDist A.carrier r p : ℕ) : ℝ) := Cayley.dist_eq _ _
  have hsq : dist (Cayley.of A s) (Cayley.of A q)
      = ((wordDist A.carrier s q : ℕ) : ℝ) := Cayley.dist_eq _ _
  have hps : dist (Cayley.of A p) (Cayley.of A s)
      = ((wordDist A.carrier p s : ℕ) : ℝ) := Cayley.dist_eq _ _
  have hrs : dist (Cayley.of A r) (Cayley.of A s)
      = ((wordDist A.carrier r s : ℕ) : ℝ) := Cayley.dist_eq _ _
  simp only [gromovProduct, hrq, hpq, hrp, hsq, hps, hrs] at key
  have hmax : ((wordDist A.carrier p q : ℕ) : ℝ)
        + ((wordDist A.carrier r s : ℕ) : ℝ)
      ≤ max (((wordDist A.carrier r q : ℕ) : ℝ)
              + ((wordDist A.carrier p s : ℕ) : ℝ))
            (((wordDist A.carrier s q : ℕ) : ℝ)
              + ((wordDist A.carrier r p : ℕ) : ℝ))
        + 2 * δ := fourPoint_of_min_gromov key
  -- the word metric is symmetric, so the two sides of the maximum are the two
  -- of the alphabet form, in the other order
  have hc1 : wordDist A.carrier r q = wordDist A.carrier q r :=
    wordDist_comm hS r q
  have hc2 : wordDist A.carrier s q = wordDist A.carrier q s :=
    wordDist_comm hS s q
  have hc3 : wordDist A.carrier r p = wordDist A.carrier p r :=
    wordDist_comm hS r p
  have hle1 := le_max_left (wordDist A.carrier p r + wordDist A.carrier q s)
    (wordDist A.carrier p s + wordDist A.carrier q r)
  have hle2 := le_max_right (wordDist A.carrier p r + wordDist A.carrier q s)
    (wordDist A.carrier p s + wordDist A.carrier q r)
  rcases le_total
      (((wordDist A.carrier r q : ℕ) : ℝ)
        + ((wordDist A.carrier p s : ℕ) : ℝ))
      (((wordDist A.carrier s q : ℕ) : ℝ)
        + ((wordDist A.carrier r p : ℕ) : ℝ)) with hcase | hcase
  · rw [max_eq_right hcase] at hmax
    have hnat : wordDist A.carrier p q + wordDist A.carrier r s
        ≤ wordDist A.carrier s q + wordDist A.carrier r p + 2 * ⌈δ⌉₊ := by
      have hR : ((wordDist A.carrier p q + wordDist A.carrier r s : ℕ) : ℝ)
          ≤ ((wordDist A.carrier s q + wordDist A.carrier r p
              + 2 * ⌈δ⌉₊ : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hR
    omega
  · rw [max_eq_left hcase] at hmax
    have hnat : wordDist A.carrier p q + wordDist A.carrier r s
        ≤ wordDist A.carrier r q + wordDist A.carrier p s + 2 * ⌈δ⌉₊ := by
      have hR : ((wordDist A.carrier p q + wordDist A.carrier r s : ℕ) : ℝ)
          ≤ ((wordDist A.carrier r q + wordDist A.carrier p s
              + 2 * ⌈δ⌉₊ : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hR
    omega

/-! ## 3.  What the core already carries -/

/-- **A hyperbolically embedded family gives a four-point constant for
`Γ(G, X ⊔ ℋ)`.**

Clause (a) of Dahmani--Guirardel--Osin's Definition 4.25 *is* hyperbolicity of
the relative Cayley graph; this only moves it from the `ℝ`-valued space form to
the `ℕ`-valued alphabet form that §4.2 consumes.  For a `HypEmbeddedCore₂` this
is `E.embedded` and nothing else --- no suitability, no loxodromic pair, no
transport, since `E.rel.alphabet` is literally the `Cayley` argument of the
clause. -/
theorem exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded {G : Type u}
    [Group G] {Λ : Type v} (D : RelGenSet G Λ)
    (hD : D.IsHyperbolicallyEmbedded) :
    ∃ δ : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ := by
  obtain ⟨δ, hδ⟩ := hD.hyperbolic
  exact ⟨⌈δ⌉₊, isFourPointHyperbolic_of_isHyperbolicSpace_cayley D.alphabet hδ⟩

end GGT
end GroupApproximation
