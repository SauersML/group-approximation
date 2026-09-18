---
rg: 2
id: f2-times-f2-has-a-quantum-rigid-free-minimal-sft
kind: claim
title: The one-ended non-amenable group F_2 × F_2 carries a free minimal subshift of finite type that is quantum rigid
distinct_from:
  free-minimal-z2-sft-is-quantum-rigid: that is the amenable Z^2 case, where an invariant measure blocks compression; this is the non-amenable rank-two case the master route rates the most informative.
  decidable-groups-lie-in-fp-free-minimal-crossed-products: that asks for rigid free minimal crossed products over overgroups of every decidable group; this is one instance over one group, which would calibrate the mechanism.
---

**OPEN.** This is gate G2(c) of `research/artifacts/gq-bh-synthesis-master-route.md`.

**Update (bh-invent-04, 2026-09-18): answered conditionally.** The Statement holds for every
`F_m × F_n` with `m, n >= 2`, over every field, by the Corollary of
`busemann-transplant-minimality-is-horospherical-minimality`. There, the Busemann transplant of the
causal diagonal-time SW version of the minimal crossing-wire shift (`sw-minimal-crossing-wire-shift-is-rigid`; a generic one-way zone fails causality) is shown to be an
SFT that is free, minimal and quantum rigid, using `tree-product-busemann-transplants-preserve-quantum-rigidity`.
It rests on unreviewed lane proofs, and the crossing-wire rigidity step is with a referee. The
status stays OPEN until those are reviewed.

## Statement

For some finite alphabet `A` there is a nonempty SFT `X ⊆ A^(F_2 × F_2)` on which `F_2 × F_2` acts
freely and minimally, and which is `D`-quantum rigid over `F_2` for some `D`.

## Payoff

- `LC(X, F_2) ⋊ (F_2 × F_2)` would be finitely presented
  (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`) and central simple
  (`free-minimal-cantor-crossed-products-are-central-simple`).
- It would be the first quantum rigid free minimal SFT over any group.
- The master route rates this single object as the one that would move the BH assessment most.

## Attempts

**Attempt 1 (bh-g2-f2f2, 2026-09-18): coset shifts over the diagonal.** Take configurations invariant
under right multiplication by the diagonal `Δ`. These are two-sided subshifts of `F_2`.
- Every quantum family then commutes on all pairs whose difference is conjugate to a short element
  (`two-sided-free-group-coset-sfts-collapse-under-cyclic-descent`, part 1), so commutation is free on
  a huge set of pairs.
- The rest must come from determinism descent (`coset-invariant-sft-rigidity-descends-along-double-cosets`).
- *Dies at finiteness* for the natural complexity. Any local determinism giving cyclic-length descent
  forces a finite subshift, because `Δ` rotates every rule into every frame (same node, part 3).

**What survives.**
- **Other complexities.** Descent over the diagonal coset space with a complexity other than cyclic
  length.
- **Coset spaces whose stabilizers fix a direction.** For example, subgroups of `Δ` fixing an end, or
  horocyclic structures. Determinism can then stay one-sided, as in Ledrappier's shift, while pair
  types are still merged.
- **The Cornulier shortcut** (`finite-double-coset-space-with-free-minimal-coset-sft`). This needs
  another group, since `F_2 × F_2` acting on `F_2` has infinitely many pair types.
- **Mozes-type SFTs over products of trees** (lane bh-g2-buildings). Local branching gives rigidity of
  a different kind, not via cosets.
