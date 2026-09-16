---
rg: 2
id: bounded-displacement-mapping-torus-sigma-infinity-open
kind: claim
title: "A mapping torus N x|_phi Z whose monodromy lifts with bounded character displacement has Sigma^infinity open at the fibre characters"
artifacts:
  - research/artifacts/zp-sigma-infinity-mapping-torus-displacement-2026-09-16.md
distinct_from:
  every-f-infinity-group-has-open-sigma-infinity: that claim asserts openness of Sigma^infinity everywhere for all groups of type F_infinity; this theorem proves openness only at the two fibre characters of a mapping torus, and only under a bounded-displacement hypothesis on a lift of the monodromy.
  bnsr-invariants-stabilize-at-cohomological-dimension: that theorem needs finite cohomological dimension and proves stabilization of the invariants; this one allows infinite cohomological dimension and proves openness at the fibre characters without any stabilization.
  non-open-sigma-infinity-needs-unbounded-sigma-depth: that lemma is point-set topology about the depth function on any group; this theorem is Novikov homology of a mapping-cone resolution and is specific to semidirect products with Z.
---

Let `N` be a group of type `F_∞`, `φ ∈ Aut(N)`, and
`G = N ⋊_φ Z = ⟨N, t | t n t^{-1} = φ(n)⟩`. Let `χ` be the fibre character
(`χ(N) = 0`, `χ(t) = 1`). Let `V = Hom(N,R)^φ`, with a norm `‖·‖`, and put
`|g|_V = sup{|ψ(g)| : ψ ∈ V, ‖ψ‖ ≤ 1}`.

**Lifts and displacement.**
- A *lift* of `θ ∈ Aut(N)` is a chain map `f : P_* → P_*` over `θ`
  (`f(nx) = θ(n) f(x)`, lifting `id_Z`). Here `P_* → Z` is a free
  `ZN`-resolution of finite type with finite bases.
- Its *displacement* `Δ(f) ∈ [0,∞]` is the supremum, over all degrees `i`, of
  `|g|_V` for `g` in the supports of the matrix entries of `f_i`.

**Claim.** Suppose that for some `k ≥ 1` there are lifts of `φ^k` and of
`φ^{-k}`, on based resolutions of `N`, with finite displacement. Put `Δ` for
the larger of the two displacements. Then:

- every character class `[aχ + ψ]` with `ψ ∈ V` and `k|a| > ‖ψ‖Δ` lies in
  `Σ^∞(G;Z)`;
- `Σ^∞(G)` contains open neighbourhoods of `[χ]` and of `[−χ]`.

The hypothesis holds in the following cases:
- when `N` is of type F (finite-length resolutions);
- when `φ` has finite order in `Out(N)`, via the lifts `x ↦ n_0^{±1} x` of
  inner automorphisms.

It depends only on the outer class of `φ`.

**Consequence for Problem 1.13.** Let `G` be a mapping torus of an `F_∞`
group. For `Σ^∞(G)` to fail to be open at a fibre character, then for every
`k ≥ 1`, at least one of `φ^k` and `φ^{-k}` must have no lift of finite
displacement on any based resolution of the fibre. In particular the monodromy
has infinite order in `Out(N)`, and `N` has a nonzero `φ`-invariant character
and is not of type F. (Artifact §3, "one-sided refinement", uses the sign
convention pinned in artifact §2 to sharpen this: failure at `[χ]` needs every
lift of every `φ^{-k}` to have infinite displacement, and failure at `[−χ]`
the same for every `φ^k`. That sharpening is not part of this claim.)

For finite order in `Out(N)` the conclusion is also consistent with
`finite-outer-order-mapping-torus-is-virtually-product`, which gives a
finite-index subgroup `N × Z`.

The proof is the mapping-cone resolution `Cone(1 − τ)` with `τ` induced by the
lift. Bounded displacement makes `τ` of uniformly positive valuation over the
Novikov ring of every nearby character, in all degrees at once. So `1 − τ` is
invertible by a geometric series, and Novikov homology vanishes in all
degrees. The artifact also proves a general "uniform certificate" version for
arbitrary characters (§5) and pins the sign convention of the
Novikov–Sikorav criterion on `BS(1,2)` (§2).
