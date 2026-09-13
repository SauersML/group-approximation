---
rg: 2
id: iid-density-iff-collapse-and-endomorphism-density
kind: claim
title: Generating i.i.d. partitions are dense exactly when the two Bernoulli shifts are isomorphic and automorphisms are dense among endomorphisms
distinct_from:
  iid-generators-dense-at-zero-rokhlin-supremum: that is the open density claim at zero supremum; this proves, over every group, that the density splits into an isomorphism and a property of one Bernoulli shift.
  bernoulli-infinite-power-iff-approximate-half-absorption: that characterizes total collapse by approximately positioned exact splittings; this characterizes density of generating i.i.d. partitions by collapse plus density of automorphisms among endomorphisms.
  iid-generators-not-dense-at-positive-rokhlin-supremum: that proves non-density at positive supremum; this derives from it that the automorphisms of every finite-base Bernoulli shift are not dense among its endomorphisms there.
---

**ESTABLISHED (unreviewed)** by [[iid-density-iff-collapse-and-endomorphism-density-proof]].

**Setting.** `G` is countably infinite. For a finite base `(K, κ)` with `H(κ) > 0` put `X_κ = (K^G, κ^G)`, with
`(g·x)(h) = x(g^-1 h)`.
- `Fac_G(X, Y)` is the set of `G`-equivariant measure-preserving Borel maps `X → Y`, modulo null sets.
  `End_G(X) = Fac_G(X, X)`, and `Aut_G(X)` is its group of invertible elements.
- On `Fac_G(X, X_λ)` put `d(φ, ψ) = µ{x : φ(x)(1_G) ≠ ψ(x)(1_G)}`.
- `Ind_λ(X)` with the metric `µ(ξ ≠ ζ)` is as in `iid-generators-dense-at-zero-rokhlin-supremum`.

1. **Dictionary.** `ξ ↦ π_ξ`, with `π_ξ(x)(g) = ξ(g^-1 x)`, is an isometric bijection
   `Ind_λ(X) → Fac_G(X, X_λ)`. The partition `ξ` generates iff `π_ξ` is an isomorphism.
2. **The topology is intrinsic.** On `End_G(X_λ)` the metric `d` induces the topology in which `φ_n → φ` iff
   `µ(φ_n^-1 A Δ φ^-1 A) → 0` for every Borel `A`. So the statement **DENSE(`X`)**: "`Aut_G(X)` is dense in
   `End_G(X)`" is an isomorphism invariant of the action.
3. **Orbits.** `Aut_G(X_κ)` acts on `Fac_G(X_κ, X_λ)` by `T·φ = φ ∘ T^-1`, by isometries. The isomorphisms form
   one orbit when there are any. For any isometric action, one dense orbit makes every orbit dense.
4. **Theorem.** Suppose `Fac_G(X_κ, X_λ) ≠ ∅`. This holds for every nonamenable `G`, by
   `nonamenable-bernoulli-shifts-are-weakly-isomorphic`. The following are equivalent:
   - (a) the generating partitions are dense in `Ind_λ(X_κ)`;
   - (b) `X_κ ≅ X_λ`, and every `Aut_G(X_κ)`-orbit in `Fac_G(X_κ, X_λ)` is dense;
   - (c) `X_κ ≅ X_λ`, and some `Aut_G(X_κ)`-orbit in `Fac_G(X_κ, X_λ)` is dense;
   - (d) `X_κ ≅ X_λ`, and DENSE(`X_λ`).

   So (a) for the pair `(κ, λ)` is equivalent to `X_κ ≅ X_λ` together with (a) for the pair `(λ, λ)`.
5. **Corollary (positive supremum).** Let `G` be nonamenable with `h^Rok_sup(G) > 0` (`∞` allowed). Then DENSE(`X_λ`)
   fails for every finite base with `H(λ) > 0`: some endomorphism of `X_λ` has a `d`-neighbourhood that contains
   no automorphism.

**Reading.**
- For each pair of bases, the exactification step of `iid-generators-dense-at-zero-rokhlin-supremum` is the
  conjunction of two statements. One is the finite-base total collapse, `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`
  at `s = 0`. The other is DENSE(`X_λ`), which concerns one Bernoulli shift and no second base entropy.
- DENSE at zero supremum is posed as `zero-supremum-bernoulli-automorphisms-dense-in-endomorphisms`. By item 5,
  a nonamenable group on which it holds for one finite base has supremum zero.
- Since `d(φ ∘ T, id) = d(φ, T^-1)`, DENSE(`X`) says: for every endomorphism `φ` and `ε > 0` some automorphism `T`
  makes `φ ∘ T` `ε`-close to the identity. Every extension of `X` realized by an endomorphism is realized by
  endomorphisms arbitrarily close to the identity.

**Model tests.**
- The hypothesis `Fac_G(X_κ, X_λ) ≠ ∅` is needed. Over `Z` with `H(λ) > H(κ)`, `Ind_λ(X_κ)` is empty, so (a) holds
  vacuously while (b)–(d) fail.
- Over `Z` with `H(λ) < H(κ)`, (a) fails by Kolmogorov–Sinai entropy and `X_κ ≇ X_λ`, as the theorem requires.
  DENSE(`X_λ`) over `Z` is expected from Ornstein theory (the Burton–Rothstein category proof of the isomorphism
  theorem); this was not re-verified from a source here.
- Over `F_2`, which is sofic and has supremum `∞`, item 5 shows DENSE fails for every finite base.

**Novelty (bounded).** Items 1–4 are elementary. The formulation through DENSE was not found in this graph
(`git grep endomorphism` over `research/`) or in Sections 1 and 9 of arXiv:1804.05269; no wider search was made.
