---
rg: 2
id: z4-has-no-monomial-embedding-in-boundary-product-hosts
kind: claim
title: No copy of F_2[Z^(r+2)] enters LC(X)⋊(Z^r×F_d) through full-group units, for any compact Q-space X and any d; so the monomial route to the boundary-product host dies at G = Z^4
distinct_from:
  crossed-product-growth-bounded-by-ball-patterns: part 3 there gives the direction "fixed-point sets with empty interior imply that k[G] embeds via full-group units". This claim proves the converse for torsion-free abelian G, namely that injectivity of the algebra map already forces a point with pairwise distinct germs. It then kills Z^(r+2) by a separator count, which the growth bound of part 2 cannot do because Z^r×F_d grows exponentially.
  decidable-algebras-embed-in-z2-sft-boundary-product-hosts: that is the OPEN target (E). This claim does not refute it. It shows that no embedding which sends G, even up to conjugacy and matrix amplification, into bisection units survives once G contains Z^4, so every surviving embedding must be non-monomial.
---

**ESTABLISHED** (lane proof, swarm-0917-w12-w12-bh-pull, 2026-09-18; elementary and self-contained; not
reviewed). Route: `z4-has-no-monomial-embedding-in-boundary-product-hosts-proof`.

## Setting

- `Q = Z^r × F_d` with `r >= 0` and `d >= 1`. `X` is any compact totally disconnected `Q`-space.
  - The host case of `decidable-algebras-embed-in-z2-sft-boundary-product-hosts` is `r = 2` and
    `X = Ω × ∂F_d`. There `LC(X, F_2) ⋊ Q = B_Ω ⊗ L_∂`.
- More generally, `𝒢` is an ample Hausdorff groupoid with a continuous cocycle `c : 𝒢 → Q` that is at most
  `m`-to-one on each source fibre `𝒢_y`.
  - For `Q ⋉ X` one has `m = 1`. For the matrix amplification `(Q ⋉ X) × R_n`, which gives `M_n` of the host,
    one has `m = n`.
- `S(𝒢)` is the Steinberg algebra over `F_2`.
- A *monomial representation* of a group `H` on a compact open `Y ⊆ 𝒢^(0)` is a map `h ↦ 1_(U_h)`. It is a
  homomorphism `H → 1_Y S(𝒢) 1_Y`, and each `U_h` is a compact open bisection with `s(U_h) = r(U_h) = Y`.
- A representation is *monomial up to conjugacy* if `w φ(·) w^(-1)` is monomial for some invertible `w`.
  - Injectivity is preserved under this, so such representations are covered as well.
  - Over `F_2`, the invertible elements supported on a single bisection are exactly the elements `1_U`.

## Statement

1. **Converse germ lemma (abelian inputs).** Let `H` be torsion-free abelian, and let `F_2[H] → S(𝒢)` be
   the linear extension of a monomial representation on `Y`. If it is injective, then some `y ∈ Y` has
   pairwise distinct germs `(U_h)_y`, `h ∈ H`. Consequently `h ↦ c((U_h)_y)` is at most `m`-to-one.
2. **Separator obstruction.** No group `H ⊇ Z^(r+2)` has a monomial representation, even up to conjugacy,
   whose linear extension `F_2[H] → S(𝒢)` is injective. In particular, `F_2[Z^4]` has no injective monomial
   representation in `M_n(B_Ω ⊗ L_∂)`, for any `Ω`, any `d` and any `n`.
3. **Sharpness.** `F_2[Z^(r+1)]` embeds monomially, via `Z^r × ⟨a⟩ ≤ Q` acting by the canonical units `v_q`.

## Consequence for (E)

The following decidable groups all contain `Z^4`, so none of them can be hosted in `B_Ω ⊗ L_∂` by the
full-group route (`crossed-product-growth-bounded-by-ball-patterns`, part 3):
- `Z^4` itself;
- `SL_n(Z)` for `n >= 4`;
- Thompson's groups `F`, `T` and `V`;
- every group containing `Z^2 × Z^2`.

This kills a whole class of approaches to (E):
- *Invariant:* the ball separation of the orbit graph, set against the `Θ(k^3)` cut of the cube `[k]^4`.
- *Where every member dies:* at the tree-centroid slab, which has size `O(k^2)`.

Every surviving embedding for `Z^4` must be non-monomial. That question is isolated in the OPEN
`f2-z4-embeds-in-z2-sft-boundary-product-hosts`, whose negation would refute (E).
