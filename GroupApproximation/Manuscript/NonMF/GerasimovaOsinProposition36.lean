import GroupApproximation.GGT.DGOProposition414General
import GroupApproximation.GGT.DGOIsolatedComponentBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Gerasimova–Osin, Proposition 3.6

Gerasimova–Osin (arXiv:1910.14524v3), §3:

> The following result is a simplified version of [DGO, Proposition 4.13].  By a geodesic
> `n`-gon in `Γ(G, 𝒜)` we mean a loop which is a concatenation of `n` geodesics; these
> geodesics are referred to as sides of `P`.
>
> **Proposition 3.6.** Let `G` be a group, `H` a subgroup of `G`.  Suppose that
> `H ↪h (G, X)` for some `X ⊆ G` and let `𝒜 = X ⊔ H`.  Then there exists a constant `C`
> satisfying the following conditions.  For any geodesic `n`-gon `p` in `Γ(G, 𝒜)` with sides
> `p₁, …, pₙ` and any `I ⊆ {1, …, n}` such that `pᵢ` is an isolated `H`-component of `p` for
> all `i ∈ I`, we have `∑_{i∈I} d̂((pᵢ)₋, (pᵢ)₊) ≤ Cn`.

## Repository form

* `H ↪h (G, X)` is `D.IsHyperbolicallyEmbedded` for `D : RelGenSet G Unit` with
  `D.fam () = H` and `D.base = X`, under Convention 3.1 (`DGO421BaseSymmetric D`).
* A geodesic `n`-gon is a closed admissible word cut into `n` sides by
  `DGOPolygonCut.IsPolygonCut`, every side realising the word distance between its vertices.
* `∑ d̂((pᵢ)₋,(pᵢ)₊) ≤ Cn` is recorded, as in `DGOUniformSumBound`, by radius witnesses:
  each span lies in the relative ball of its radius and the radii sum to at most `Cn`.

The proof is Dahmani–Guirardel–Osin's Proposition 4.14 at `(1,0)`
(`dgoProposition414Uniform`): a component filling a geodesic side is a single edge
(`isComp_eq_succ_of_geodesic`), and a geodesic side is `(1,0)`-quasi-geodesic.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (Gerasimova–Osin's §3).  Certifies no printed
sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace GerasimovaOsinWords

open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.WordMetric

universe u

/-- **Gerasimova–Osin, Proposition 3.6**, as a statement. -/
def GerasimovaOsinProposition36Statement : Prop :=
  ∀ (G : Type u) [Group G] (D : RelGenSet G Unit),
    DGO421BaseSymmetric D → D.IsHyperbolicallyEmbedded →
    ∃ C : ℕ, ∀ (n : ℕ) (v : G) (word : List (RelLetter G Unit)) (cut : ℕ → ℕ)
      (I : Finset ℕ),
      (∀ a ∈ word, D.IsLetter a) → RelLetter.listVal word = 1 →
      IsPolygonCut n word cut →
      (∀ s : ℕ, s < n → ∀ p q : ℕ, cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
        q - p ≤ wordDist D.alphabet.carrier (vertex v word p) (vertex v word q)) →
      (∀ s ∈ I, s < n) →
      (∀ s ∈ I, IsComp () word (cut s) (cut (s + 1))) →
      (∀ s ∈ I, IsIsolated D.fam () v word (cut s)) →
      ∃ r : ℕ → ℕ,
        (∀ s ∈ I, (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) ∈ D.relBall () (r s)) ∧
        ∑ s ∈ I, r s ≤ C * n

/-- **Gerasimova–Osin, Proposition 3.6.** -/
theorem gerasimovaOsinProposition36 : GerasimovaOsinProposition36Statement.{u} := by
  intro G _ D hbase hD
  obtain ⟨C, -, hsum, -⟩ :=
    dgoProposition414Uniform G Unit D hD.hyperbolic hbase 1 0 le_rfl le_rfl
  refine ⟨C, fun n v word cut I hlet hclosed hcut hgeo hI hcomp hiso => ?_⟩
  refine hsum n v word cut I (fun _ => ()) hlet hclosed hcut hI ?_ hcomp hiso ?_
  · intro s hs
    exact isComp_eq_succ_of_geodesic D () v hlet (hcomp s hs)
      (hgeo s (hI s hs) (cut s) (cut (s + 1)) le_rfl (hcut.mono s) le_rfl)
  · intro s hs _ p q hp hpq hq
    have h := hgeo s hs p q hp hpq hq
    have hcast : ((q - p : ℕ) : ℝ)
        ≤ ((wordDist D.alphabet.carrier (vertex v word p) (vertex v word q) : ℕ) : ℝ) := by
      exact_mod_cast h
    simp only [div_one, sub_zero]
    exact hcast

end GerasimovaOsinWords
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.GerasimovaOsinWords.gerasimovaOsinProposition36
