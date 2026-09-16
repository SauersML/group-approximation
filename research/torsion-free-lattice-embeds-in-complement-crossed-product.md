---
rg: 2
id: torsion-free-lattice-embeds-in-complement-crossed-product
kind: claim
title: A torsion-free lattice's group factor is a corner subalgebra of the crossed product of a complementary discrete subgroup acting on the lattice quotient
distinct_from:
  hecke-corner-uniform-lattice-transfers-embeddability: that pushes Connes embeddability from a hyperlinear uniform lattice to the Hecke algebras of the ambient group, which for products of trees are always embeddable (its HC5); this pulls embeddability back to an arbitrary torsion-free lattice from the crossed product of a complementary subgroup on the lattice quotient, an algebra that is not automatically embeddable.
  measure-full-group-subgroups-hyperlinear-if-crossed-product-ce: that needs an essentially free Cantor action and embeds whole topological full-group elements; this needs no freeness and realizes a lattice of the ambient group by partial translations inside a corner, through the cocycle of the coupling.
  product-tree-lattices-in-paunescu-class-iff-f2xf2: that transfers soficity of all actions by measure-equivalence invariance; this is an explicit trace-preserving corner embedding of one group factor, for any locally compact group with a compact open subgroup and a complementary discrete subgroup.
  dense-s-arithmetic-translation-algebra-is-amplified-profinite: that computes the translation algebra of an S-arithmetic group on the whole p-adic group, with infinite measure and a dense acting group; this uses a discrete complement acting on a finite-measure lattice quotient and extracts the lattice's group factor from a corner.
  coinduction-retains-crossed-product-not-relation: that identifies a subgroup crossed product inside a coinduced crossed product; this embeds the group factor of a different group, a lattice of the ambient group, in a corner of the complement's crossed product.
artifacts:
  - research/artifacts/fournier-facio-simple-factor-corner-2026-09-16.md
---

**ESTABLISHED** by route `torsion-free-lattice-complement-crossed-product-proof`. Not
independently reviewed. No novelty is claimed: this is the von Neumann shadow of the standard
measure-equivalence coupling of two lattices.

**Setting.**

- `H` is a locally compact second countable group and `K ≤ H` is compact open.
- `Λ ≤ H` is a subgroup with `H = ΛK` and `Λ ∩ K = {1}`. Then `Λ` is countable and discrete.
- `S ≤ H` is a lattice with `S ∩ K = {1}`. This is automatic if `S` is torsion-free.
- `μ` is the `H`-invariant probability measure on `X = H/S`.
- `M = L^∞(X, μ) ⋊ Λ` is the crossed product with its canonical trace `τ`. **No freeness is
  assumed.**

**Theorem.** Let `p = 1_{KS/S}`. Then `τ(p) > 0`, and there is a group homomorphism
`w : S → U(pMp)` with

```text
τ(w_s) = δ_{s,1} τ(p)      for all s ∈ S.                              (CL1)
```

Hence `L(S)` embeds trace-preservingly into `pMp` with trace `τ(p)^{-1} τ`. So if `M` is
Connes-embeddable, then `L(S)` is Connes-embeddable.

**Formula.**

- Write `ks = λ(k,s) κ(k,s)` with `λ(k,s) ∈ Λ` and `κ(k,s) ∈ K`.
- Put `A_{s,λ} = {kS : k ∈ K, λ(k,s) = λ}`. These are clopen, and only finitely many are
  nonempty for each `s`.
- The unitary is `w_s = u_{s^{-1}}`, where `u_s = Σ_λ v_{λ^{-1}} 1_{A_{s,λ}}`.

**Consequence.** By `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower`, a
torsion-free lattice `S` in `H` is hyperlinear as soon as `L^∞(H/S) ⋊ Λ` is
Connes-embeddable. Contrapositively, a non-hyperlinear torsion-free lattice makes the crossed
product of every complementary `Λ` on its quotient non-Connes-embeddable. For products of
trees this is used in `tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce`.
