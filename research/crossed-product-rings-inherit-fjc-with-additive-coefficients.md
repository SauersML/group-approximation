---
rg: 2
id: crossed-product-rings-inherit-fjc-with-additive-coefficients
kind: claim
title: For a crossed product ring R_(α,τ)G, Farrell–Jones with additive coefficients for G assembles K(R_(α,τ)G) from the crossed products over virtually cyclic subgroups
distinct_from:
  virtually-poly-z-groups-satisfy-fjc-with-additive-coefficients: that imports the conjecture for virtually poly-Z groups; this identifies the values of the coefficient system when it comes from a crossed product ring, for any group G.
  e1-ring-spectrum-fj-for-geometric-and-linear-classes: that is the ring-spectrum form for untwisted group rings; this is the additive-category form, specialized to crossed products with an action and a cocycle.
artifacts:
  - research/artifacts/leavitt-tensor-k-theory-farrell-jones-2026-09-12.md
---

**ESTABLISHED (literature import).** Let `R` be a ring and `G` a group. Let
`α : G -> Aut(R)` with `α_e = id`, and let `τ : G × G -> R^x` satisfy

```text
τ_(g,h) τ_(gh,k) = α_g(τ_(h,k)) τ_(g,hk),    τ_(g,h) α_(gh)(r) = (α_g ∘ α_h)(r) τ_(g,h).
```

The crossed product ring `R_(α,τ)G` is `RG` as an abelian group, with
`(r g)(s h) = r α_g(s) τ_(g,h) gh`.

1. **Coefficients.** There is an additive category `A_(α,τ)` with a right
   `G`-action such that, for every orbit `G/H`, `A_(α,τ) ∗_G G/H` is equivalent
   to the category of finitely generated free `R_(α|,τ|)H`-modules. So for every
   `n ∈ Z`:
   - `H_n^G(G/H; K_(A_(α,τ))) ≅ K_n(R_(α|,τ|)H)`;
   - `H_n^G(pt; K_(A_(α,τ))) ≅ K_n(R_(α,τ)G)`.
2. **Assembly.** If `G` satisfies the `K`-theoretic Farrell–Jones conjecture with
   additive categories as coefficients, with respect to `VCyc`, then
   `H_n^G(E_VCyc G; K_(A_(α,τ))) -> K_n(R_(α,τ)G)` is bijective for every
   `n ∈ Z`.

**Source.** A. Bartels and H. Reich, *Coefficients for the Farrell–Jones
Conjecture*, arXiv:math/0510602. Read from the e-print TeX source on MSI,
2026-09-12.
- **Section "Crossed products"** gives the definition above: "The crossed
  product ring R_{α,τ}G is as an additive group RG, but is equipped with a
  twisted multiplication ... (rg)·(sh) = r α_g(s) τ_{g,h} gh".
- **Corollary `cor:crossed-product-in-category-language`:** "there exists an
  additive category A_{α,τ} with a right G-action, such that for every orbit G/H
  the category A_{α,τ} ∗_G G/H and the category F^f(R_{α|,τ|}H) of finitely
  generated R_{α|,τ|}H-modules are equivalent. ... In particular there is for
  every G/H and every n ∈ Z an isomorphism
  K_n(A_{α,τ} ∗_G G/H) ≅ K_n(R_{α|,τ|}H)."
- **The paragraph after it:** "the G-equivariant homology theory
  H_*^G(−; K_{A_{α,τ}}) evaluated on an orbit G/H is isomorphic to
  K_*(R_{α|,τ|}H)". Conjecture `con:FJ-for-crossed-product` is stated as "the
  following special case" of the conjecture with coefficients.

**Part 2.** Part 2 is the conjecture with coefficients applied to the single
additive `G`-category `A_(α,τ)`. Bartels–Farrell–Lück arXiv:1101.0469 state
their definition "for any additive G-category A". Their remark "Relevance of the
additive categories as coefficients" reads: "The versions of the Farrell-Jones
Conjecture appearing in Definition def:K-theoretic_Farrell-Jones_Conjecture ...
are formulated and analyzed in [Bartels-Lueck(2009coeff)],
[Bartels-Reich(2007coeff)]. They encompass the versions for group rings RG over
arbitrary rings R, where one can built in a twisting into the group ring or
treat more generally crossed product rings R ∗ G".

The journal reference was not checked.
