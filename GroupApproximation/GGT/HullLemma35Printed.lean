import GroupApproximation.GGT.WPDHyperbolicallyEmbedded

/-!
# Hull's Lemma 3.5 and the free factors of a free product, printed

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 (M. Hull, *Small cancellation in acylindrically hyperbolic groups*,
arXiv:1308.4345v2, §7) takes `F = G₁ ∗ G₂`, identifies `G₁` and `G₂` with their images in `F`,
and continues:

> Since `{G₁, G₂} ↪h F`, Lemma 3.5 gives that `{⟨f₁⟩, ⟨f₂⟩, ⟨h₁⟩, ⟨h₂⟩} ↪h F`.

This module states the two facts that sentence uses, at printed generality:

* `PrintedFreeFactorsHypEmbedded`: `{G₁, G₂} ↪h G₁ ∗ G₂` for all groups `G₁` and `G₂`;
* `PrintedHullLemma35`: Hull's Lemma 3.5, for every `n` and every `m₁, …, mₙ`.

`IsHypEmbeddedFamily` is Hull's `{H_λ}_{λ∈Λ} ↪h G`. It is stated against the repository's
`RelGenSet.IsHyperbolicallyEmbedded`, which is Hull's Definition 3.1. Both are Dahmani, Guirardel
and Osin's Definition 4.25.

`HullSC.FreeProductUnionGeometryStatement` and the `HullSCUnionGeometry*` modules give the free
product only the manuscript's union alphabet over `Type`. `GGT/HullLemma35FreeFactors.lean`
proves `PrintedFreeFactorsHypEmbedded` (`printedFreeFactorsHypEmbedded`).
`GGT/HullLemma35Closed.lean` proves `PrintedHullLemma35` (`printedHullLemma35`).
-/

namespace GroupApproximation
namespace GGT

universe u w

/-- **`{H_λ}_{λ∈Λ} ↪h G`**, Hull, Definition 3.1 (arXiv:1308.4345v2, §3):

> We write `{H_λ}_{λ∈Λ} ↪h (G, X)` to mean that `{H_λ}_{λ∈Λ}` is hyperbolically embedded in `G`
> with respect to `X` or simply `{H_λ}_{λ∈Λ} ↪h G` if we do not need to keep track of the set `X`,
> that is `{H_λ}_{λ∈Λ} ↪h (G, X)` for some `X ⊆ G`.

The relative generating set `D` carries `X` as `D.base` and the family as `D.fam`. -/
def IsHypEmbeddedFamily (G : Type u) [Group G] {Λ : Type w} (H : Λ → Subgroup G) : Prop :=
  ∃ D : RelGenSet G Λ, D.fam = H ∧ D.IsHyperbolicallyEmbedded

/-- **Hull, Lemma 3.5** (arXiv:1308.4345v2, §3, p. 12), printed as "a simplification of
[DGO, Proposition 4.35]" and without a proof:

> Suppose `{H_i}_{i=1}^n ↪h G`, and for each `1 ≤ i ≤ n`, `{K^i_j}_{j=1}^{m_i} ↪h H_i`.
> Then `{K^i_j | 1 ≤ i ≤ n, 1 ≤ j ≤ m_i} ↪h G`.

`K^i_j` is a subgroup of `H_i`. As a member of the family in `G` it is its image under the
inclusion `H_i ≤ G`, and the family is indexed by the pairs `(i, j)`. -/
def PrintedHullLemma35 : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ) (H : Fin n → Subgroup G) (m : Fin n → ℕ)
    (K : ∀ i : Fin n, Fin (m i) → Subgroup (H i)),
    IsHypEmbeddedFamily G H → (∀ i : Fin n, IsHypEmbeddedFamily (H i) (K i)) →
      IsHypEmbeddedFamily G
        (fun p : (i : Fin n) × Fin (m i) => (K p.1 p.2).map (H p.1).subtype)

/-- **The free factors are hyperbolically embedded in the free product**, the clause
"Since `{G₁, G₂} ↪h F`" of Hull's proof of Corollary 7.4 (arXiv:1308.4345v2, §7):

> Let `F = G₁ ∗ G₂`, and let `ιᵢ : Gᵢ → F` be the natural inclusion. We will identify `G₁` and
> `G₂` with their images in `F`. [...] Since `{G₁, G₂} ↪h F`, Lemma 3.5 gives that
> `{⟨f₁⟩, ⟨f₂⟩, ⟨h₁⟩, ⟨h₂⟩} ↪h F`.

The factors are the ranges of `Monoid.Coprod.inl` and `Monoid.Coprod.inr`. Hull's `G₁` and `G₂`
are acylindrically hyperbolic, but the clause holds, and is stated here, for all groups. -/
def PrintedFreeFactorsHypEmbedded : Prop :=
  ∀ (G₁ G₂ : Type u) [Group G₁] [Group G₂],
    IsHypEmbeddedFamily (Monoid.Coprod G₁ G₂)
      ![(Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂).range,
        (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂).range]

end GGT
end GroupApproximation
