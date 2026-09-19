import GroupApproximation.GGT.DGOProposition433Finite
import GroupApproximation.GGT.ElementaryHypEmbedded

/-!
# Why Hull's non-commensurability carries a conjugator

Hull's `nonelsub`, `yi` and `heGX` all quantify over **non-commensurable**
loxodromic elements, and his non-commensurability forbids

    c⁻¹ * f ^ p * c = g ^ q      for every `c` and all nonzero `p`, `q`,

not merely `f ^ p = g ^ q`.  The weaker form -- no conjugator -- is the one the
repository's `GGT.Elementary.IndependentOfNoCommonZpow` uses, so it is the one
that comes to hand, and it is **wrong here**.

This module proves that, rather than asserting it.  The weak form is not merely
weaker: a family satisfying it can consist of **conjugates**, and

> conjugate members can never both sit in a hyperbolically embedded family.

`not_isHyperbolicallyEmbedded_of_conj_fam` is that statement, and it is two
lines on Dahmani-Guirardel-Osin's Proposition 4.33(a)
(`GGT.finite_conj_inter_of_ne`, proved): for distinct indices and *any*
conjugator the twisted intersection is finite, while for `H_mu = c H_lam c⁻¹`
that intersection is all of `H_lam`.
`not_isHyperbolicallyEmbedded_elementaryClosure_conj` specialises it to `E(f)`
and `E(c f c⁻¹)`, which is the configuration the weak clause admits and Hull's
excludes.

## The consequence worth carrying away

**The repository's usual tool for producing independent pairs produces exactly
this excluded configuration.**  `GGT.Elementary.independent_conj_of_notMem_elementaryClosure`
and `exists_independent_conjugate` build the second element as `h g h⁻¹`; those
elements are independent, and they are Hull-commensurable, so their elementary
closures are provably *not* jointly hyperbolically embedded.  Non-commensurable
families cannot be manufactured by conjugation at all.

Hull's own architecture agrees: his non-commensurable elements come from
Dahmani-Guirardel-Osin's Corollary 6.12 (`gh^{n₁}, gh^{n₂}, gh^{n₃}` for
sufficiently large exponents), never from conjugation.  That makes 6.12 the
sole source of non-commensurability in this chain.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.Elementary

universe u v w

/-- **Conjugate members cannot both sit in a hyperbolically embedded family.**

If the `mu`-th member is the `c`-conjugate of the `lam`-th and the latter is
infinite, the family is not hyperbolically embedded: Proposition 4.33(a) makes
the twisted intersection finite, and here that intersection is the whole of the
`lam`-th member. -/
theorem not_isHyperbolicallyEmbedded_of_conj_fam {G : Type u} [Group G]
    {Λ : Type w} [Finite Λ] (D : GGT.RelGenSet G Λ) {lam mu : Λ}
    (hne : lam ≠ mu) (c : G)
    (hconj : ∀ x : G, x ∈ D.fam lam ↔ c * x * c⁻¹ ∈ D.fam mu)
    (hinf : ((D.fam lam : Subgroup G) : Set G).Infinite) :
    ¬ D.IsHyperbolicallyEmbedded := by
  intro hemb
  refine hinf (Set.Finite.subset (GGT.finite_conj_inter_of_ne D hemb hne c⁻¹) ?_)
  intro x hx
  have hxmem : x ∈ D.fam lam := hx
  refine ⟨hxmem, ?_⟩
  rw [inv_inv]
  exact (hconj x).mp hxmem

/-- **The model test of Hull's conjugator.**  For a loxodromic `f` the family
`{E(f), E(c f c⁻¹)}` is never hyperbolically embedded --- yet `f` and
`c f c⁻¹` satisfy the *weak* non-commensurability clause whenever no power of
one is literally a power of the other.  So the weak clause admits families that
`heGX` provably cannot hold for, and the conjugator is forced. -/
theorem not_isHyperbolicallyEmbedded_elementaryClosure_conj {G : Type u}
    [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (D : GGT.RelGenSet G Bool) {f c : G} {x : X} (hf : IsLoxodromic f x)
    (h0 : D.fam false = elementaryClosure f)
    (h1 : D.fam true = elementaryClosure (c * f * c⁻¹)) :
    ¬ D.IsHyperbolicallyEmbedded := by
  have hne : (false : Bool) ≠ true := by decide
  refine not_isHyperbolicallyEmbedded_of_conj_fam D hne c ?_ ?_
  · intro y
    rw [h0, h1]
    exact ⟨fun hy => mem_elementaryClosure_conj hy,
      fun hy => mem_elementaryClosure_of_conj_mem hy⟩
  · rw [h0]
    exact infinite_elementaryClosure_of_isLoxodromic hf

end HullSC
end GroupApproximation
