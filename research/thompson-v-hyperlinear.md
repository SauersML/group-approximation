---
rg: 2
id: thompson-v-hyperlinear
kind: claim
title: Thompson's group V is hyperlinear
distinct_from:
  thompson-v-not-hyperlinear: that is the opposite answer, which selects the HS-stable Steinberg branch; this is the answer every construction on the unstable branch must also produce.
  leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear: that is the stakes lemma saying the Leavitt hyperlinear branch forces this claim; this is the claim itself, a named open problem.
---

**OPEN.** Thompson's group `V = G_(2,1)` embeds into a tracial matrix
ultraproduct `prod_omega (M_n, tr_n)`.

By `thompson-v-ce-one-word-trace-face-is-binary`, this holds exactly when one
fixed word `w != 1` has squared normalized HS energy bounded away from zero in
models of one finite presentation with relator defect tending to zero. Once it
holds, every nontrivial word has energy `2t` for one common `t > 0`, and after
cutting to the regular summand `t = 1`.

It is necessary for `leavitt-steinberg-hs-unstable` and for
`binary-leavitt-unit-group-hyperlinear`
(`leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear`, now also through
`Q = EL_4(L) = L^x`).

## Constraints on any model

- **No Kazhdan rigidity to fight.** `V` has the Haagerup property (Farley 2003),
  so it contains no infinite Kazhdan subgroup and no compression criterion of
  this graph applies inside it.
- **Models cannot be spatial.** Suppose a normalized-trace model carries
  projections `P_alpha` for binary cylinders, intertwined by the prefix
  transpositions (`(alpha beta) P_alpha (alpha beta)^* ~ P_beta`) and refined
  (`P_alpha ~ P_(alpha 0) + P_(alpha 1)`, `P_0 + P_1 ~ I`), each up to `O(delta)`
  in normalized trace. Then all proper cylinder traces agree up to `O(delta)`.
  Refinement gives `tr(P_alpha) ~ 2 tr(P_alpha)`, so they are all `O(delta)`,
  contradicting `tr(P_0) + tr(P_1) ~ 1`. This is the finite shadow of the
  absence of a `V`-invariant probability measure on the Cantor set. Truncating
  the tree-vertex (Cuntz) representation fails for the same reason, since its
  Schreier graph is coarsely the binary tree and has boundary of positive
  proportion. A hyperlinear model must be non-spatial, close in spirit to a
  finite approximation of the regular representation.
- **Separation is uniform.** Every nontrivial word eventually carries the same
  energy, so a construction only needs to certify one marked word, for example
  `a = (00 01)` in the Bleak--Quick presentation. That same word is the target
  of every collapse lane (`thompson-v-one-word-strict-hs-ceiling`).

## Attempts

- **Truncated tree-vertex models.** Restrict the almost action of `V` on finite
  binary words to words of length at most `M` and rewire the boundary. This
  dies at the first length-changing generator. The Schreier graph is coarsely
  the binary tree, so every finite set has boundary of positive proportion and
  the relator defect stays bounded below.
- **Spatial cylinder models.** These are degenerate by the trace count above.
- **Closure permanence.** Limits in the space of marked groups, and amalgams or
  HNN extensions over amenable subgroups, preserve hyperlinearity. `V` is
  finitely presented and simple, so every marked group close enough to `V` is
  `V` itself, and there is no decomposition over a proper amenable subgroup to
  exploit. This dies before it starts.
- **Gluing regular packet models.** Every generator lies in a finite packet
  `Sym(P)` for a non-uniform complete prefix code `P`, and the regular
  representation of `Sym(P)` is non-spatial. The gluing dies at coherence.
  Packets for different generators need different codes, and their regular
  models must be identified around the refinement squares of the code poset.
  In dimension `d`, compact packing (`thompson-v-r5-cap-implies-one-word-collapse`)
  forces this coherence to fail at order one on packets of size above about
  `d`, when the named transpositions are literal conjugates of the marked word.
  A model must be regular on shallow packets and order-one non-multiplicative
  at depth about `log_2 d`.
- **Operator-norm stability.** Fournier-Facio--Rangarajan give uniform stability
  for submultiplicative norms. Since `V` has no nontrivial finite-dimensional
  representation, uniform almost-representations are near trivial. That says
  nothing about pointwise normalized-HS models, so it neither produces nor
  excludes the models this claim needs.
- **Numerical search from generic starts** (lane `q34-v-models`, 2026-09-12).
  - **Setup:** Riemannian descent and basin hopping on the Bleak--Quick
    presentation, with `u^6 = v^3 = 1` exact and `u^3` at energy `2`.
  - **Result:** both plateau at a maximal relator HS defect of about 1.1 for
    `d` up to 48.
  - **Control:** the same search also fails to solve a planted `S_5` control
    that has exact models at every `d = 6k`. So finding no near-solutions is
    not evidence against this claim. A usable search must first solve that
    control from generic starts.
  - **Artifact:** `research/artifacts/thompson-v-hs-probe-calibration-2026-09-12.md`.
