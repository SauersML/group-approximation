---
rg: 2
id: central-extension-haagerup-from-measurable-euler-splitting
kind: claim
title: "A central Z-extension G of a Haagerup group Q is Haagerup as soon as the extension splits measurably (a real cocycle beta with beta(z,.) = 1) over some nonsingular Q-space whose Koopman representation has almost invariant vectors"
distinct_from:
  cantor-integer-maps-central-growth-criterion: that is a growth criterion for cnd functions on C(C,Z) ⋊ V along the central direction; this is a measure-theoretic sufficient condition for any central Z-extension, with no cnd function on G given in advance
  lifted-thompson-t-extractable-cocycles-bounded-on-centre: that kills cocycles extracted from circle measures; this is a positive criterion, and its hypothesis provably fails over every space mapping to S^1 (perfect-extension-splittings-are-not-uniformly-integrable)
  haagerup-splits-as-coset-plus-subgroup-properness: that splits properness of one cnd function into a coset part and a subgroup part; this builds the witness from a skew-product space and needs no given cnd function
artifacts: []
---

**ESTABLISHED** by `central-extension-haagerup-from-measurable-euler-splitting-proof`.

**Setting.** `G` is a countable group, `z ∈ G` is central of infinite order, `p : G → Q = G/⟨z⟩`.
`(X, μ)` is a standard σ-finite measure space with a nonsingular action of `Q` (so `G` acts
through `p`). Write `RN_q = d(q_*μ)/dμ` and let `κ` be the Koopman representation
`(κ(q)ξ)(x) = RN_q(x)^{1/2} ξ(q^{-1}x)` on `L²(X, μ)`.

**Statement.** Assume
1. `Q` has the Haagerup property;
2. `κ` has almost invariant vectors: unit vectors `ξ_n` with `‖κ(q)ξ_n − ξ_n‖ → 0` for all `q`;
3. (measurable Euler splitting) there is a measurable `β : G × X → R` with
   `β(gh, x) = β(g, hx) + β(h, x)` for all `g, h ∈ G` and a.e. `x`, and `β(z, x) = 1` a.e.

Then `G` has the Haagerup property. No integrability of `β` is required.

**Calibration.**
- `X = Q` with counting measure always satisfies 3 (use a set-theoretic section `Q → G`), and
  satisfies 2 iff `Q` is amenable; this recovers "amenable-by-cyclic central extensions are
  amenable".
- A single point never satisfies 3 unless `z` survives in `Hom(G, R)`.
- The obstruction side is `perfect-extension-splittings-are-not-uniformly-integrable`: when
  `Hom(G, R)` kills `z`, hypotheses 2 and 3 can only hold together with a heavy-tailed `β`.

## Attempts

- 2026-09-18 (swarm-0917-w9-w9-nv-follow): proved as stated; see the proof route.
