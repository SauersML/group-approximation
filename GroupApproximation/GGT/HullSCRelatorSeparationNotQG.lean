import GroupApproximation.GGT.HullSCRelatorSeparationConnector
import GroupApproximation.GGT.OsinPenetration

/-!
# Hull's relator, as modelled over one subgroup, is not quasi-geodesic

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, §5 and §6;
Osin, *Acylindrically hyperbolic groups*, §4.

`HullSC.relatorWord p h ms` is `p · h^{m₁} ⋯ h^{m_k}` over `Λ = Unit`, so all its
`H`-letters carry the one index and are consecutive.  Two things follow, and the
second kills the model.

* The `H`-letters form a single component
  (`GGT/HullSCRelatorSeparationComponent.lean`).
* That component **runs between two vertices at distance one**.  Its endpoints
  are `p.prod` and `p.prod · h^{Σ mᵢ}`, and `h^{Σ mᵢ}` lies in `H`, hence is a
  single letter of `X ⊔ H`, hence a single edge of `Γ(G, X ⊔ H)`.  So the word
  spends `k` letters crossing a distance of one.

`not_quasiGeodesic_relatorWord` is that statement: for every `mu` and `b`, once
`ms.length > mu (1 + b)` the relator violates the quasi-geodesic lower bound
`(j - i)/mu - b ≤ d(vertexᵢ, vertexⱼ)` at `i = |p|`, `j = |p| + |ms|`.  The
constants are quantified outside the relator, and the estimate is free to take
`ms` as long as it likes, so no choice of constants rescues it.

Hull's Theorem 5.1 runs Dahmani--Guirardel--Osin's Theorem 5.3 on the cone-off,
and the isolated-component bound its proof rests on
(`GGT.OsinComponents.IsolatedComponentBound`) is stated for polygons with
quasi-geodesic sides.  A relator that is not quasi-geodesic is not a side such a
polygon can have, so the estimate has nothing to run on.

## A risk this records, short of a refutation

`RelWord.IsSmallCancellation` has six clauses -- admissibility, closure under
inversion and rotation, length, depth, small pieces -- and none of them is a
quasi-geodesicity clause.  So `HullSC.HullQuotientStatement`, which quantifies
over *every* family meeting those six, ranges over families Hull's proof does
not cover, and the symmetrized closure of `relatorWord` is one of them: it meets
every shape clause and is not quasi-geodesic.  That does not show
`HullQuotientStatement` is false, and nothing here claims it; what it shows is
that the statement is not the theorem Hull proves, and that the pair (quotient
statement, relator statement) does not compose for the reason his proof would.

## What the model is missing

Hull takes `u = h₁^{n₁} h₂^{n₂} ⋯` in **independent** loxodromics, which in the
hyperbolically embedded picture means the letters alternate between *different*
members of the family `{H_λ}`.  Then consecutive letters lie in different
components, no two of them merge, and the word is quasi-geodesic for constants
depending on the family alone.  `HullSC.HypEmbeddedCore` carries one subgroup
and `Λ = Unit`, so that alternation cannot be written down, and the relator
degenerates to a single syllable.

This is the same shape as the two-syllable trap already recorded against the
weighted Greendlinger route: a relator whose syllables merge carries no
cancellation information.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Vertex

variable {G : Type u} [Group G] {Λ : Type w}

/-- The vertex reached after reading the whole of the first part of a
concatenation. -/
theorem vertex_append_left (v : G) (l₁ l₂ : List (GGT.RelLetter G Λ)) :
    GGT.OsinComponents.vertex v (l₁ ++ l₂) l₁.length
      = v * GGT.RelLetter.listVal l₁ := by
  induction l₁ generalizing v with
  | nil =>
      show GGT.OsinComponents.vertex v l₂ 0 = v * GGT.RelLetter.listVal []
      rw [GGT.OsinComponents.vertex_zero, GGT.RelLetter.listVal_nil, mul_one]
  | cons a t ih =>
      show GGT.OsinComponents.vertex v (a :: (t ++ l₂)) (t.length + 1)
        = v * GGT.RelLetter.listVal (a :: t)
      rw [GGT.OsinComponents.vertex_cons_succ, ih, RelWord.listVal_cons,
        mul_assoc]

end Vertex

/-! ## The relator crosses a distance of one in `|ms|` letters -/

section NotQG

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The component of the relator spans a single edge.**  Its endpoints are
`p.prod` and `p.prod · h^{Σ mᵢ}`, and the second factor lies in `H`, so it is a
letter of `X ⊔ H`. -/
theorem wordDist_relatorWord_component_le_one (E : HypEmbeddedCore A N)
    (p : List G) (ms : List ℕ) :
    wordDist E.rel.alphabet.carrier p.prod (p.prod * E.lox ^ ms.sum) ≤ 1 := by
  have hmem : E.lox ^ ms.sum ∈ E.rel.fam () := by
    have hfam : E.rel.fam () = E.H := by rw [E.fam_eq]
    rw [hfam]
    exact E.H.pow_mem E.lox_mem ms.sum
  unfold wordDist
  rw [inv_mul_cancel_left]
  exact wordNorm_le_one_of_mem
    (GGT.RelGenSet.fam_subset_alphabet E.rel () hmem)

/-- **Hull's relator, over one subgroup, is not `(mu, b)`-quasi-geodesic.**

At `i = |p|` and `j = |p| + |ms|` the two vertices are `p.prod` and
`p.prod · h^{Σ mᵢ}`, at distance at most one, while the index gap is `|ms|`.  So
the lower bound `(j - i)/mu - b ≤ d` forces `|ms| ≤ mu (1 + b)`, and the
estimate is free to take `ms` longer.

The constants are quantified before the relator, which is what makes this a
refutation rather than a bound: no `(mu, b)` depending on `E` alone survives. -/
theorem not_quasiGeodesic_relatorWord (E : HypEmbeddedCore A N) (p : List G)
    (ms : List ℕ) (mu b : ℝ) (hmu : 0 < mu)
    (hlong : mu * (1 + b) < (ms.length : ℝ)) :
    ¬ (∀ i j : ℕ, i ≤ j → j ≤ (relatorWord p E.lox ms).length →
        ((j - i : ℕ) : ℝ) / mu - b ≤
          (wordDist E.rel.alphabet.carrier
            (GGT.OsinComponents.vertex 1 (relatorWord p E.lox ms) i)
            (GGT.OsinComponents.vertex 1 (relatorWord p E.lox ms) j) : ℝ)) := by
  intro hqg
  have hlen : (relatorWord p E.lox ms).length = p.length + ms.length :=
    length_relatorWord p E.lox ms
  have hvi : GGT.OsinComponents.vertex 1 (relatorWord p E.lox ms) p.length
      = p.prod := by
    have h := vertex_append_left (1 : G) (p.map GGT.RelLetter.base)
      (ms.map fun r => (GGT.RelLetter.comp () (E.lox ^ r) : GGT.RelLetter G Unit))
    rw [List.length_map, listVal_map_base, one_mul] at h
    exact h
  have hvj : GGT.OsinComponents.vertex 1 (relatorWord p E.lox ms)
      (p.length + ms.length) = p.prod * E.lox ^ ms.sum := by
    have h := GGT.OsinComponents.vertex_length (1 : G) (relatorWord p E.lox ms)
    rw [hlen, one_mul, listVal_relatorWord] at h
    exact h
  have hkey := hqg p.length (p.length + ms.length) (by omega) (by omega)
  rw [hvi, hvj] at hkey
  have hsub : p.length + ms.length - p.length = ms.length := by omega
  rw [hsub] at hkey
  have hcast : (wordDist E.rel.alphabet.carrier p.prod
      (p.prod * E.lox ^ ms.sum) : ℝ) ≤ 1 := by
    exact_mod_cast wordDist_relatorWord_component_le_one E p ms
  have h1 : ((ms.length : ℕ) : ℝ) / mu ≤ 1 + b := by linarith
  have h2 : ((ms.length : ℕ) : ℝ) ≤ (1 + b) * mu := (div_le_iff₀ hmu).mp h1
  have h3 : (1 + b) * mu = mu * (1 + b) := mul_comm _ _
  linarith

end NotQG

end HullSC
end GroupApproximation
