---
rg: 2
id: kt-free-lamp-hnn-group-is-hyperlinear
kind: claim
title: The centralizing HNN extension of the Kun--Thom pair, the free-lamp group over the coset space, is hyperlinear
distinct_from:
  kt-double-mixed-word-trace-selection: that is equivalent to hyperlinearity of the double `G *_Gamma G`; this asks for hyperlinearity of the larger group `G *_Gamma (Gamma x Z) = F(G/Gamma) x| G`, which contains the double and all its iterated amalgams, so it is a strictly stronger open statement.
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that is the general equivalence, for any pair, between hyperlinearity of this HNN group and an amalgamated-free Haar unitary in some trace-preserving model of the base; this is its open instance for the Kun--Thom pair, recorded as the positive side of the free-lamp route.
  hyperlinear-wreath-model: that is the coset wreath with commuting `C_2` lamps, a quotient of this group (free lamp to base lamp); hyperlinearity is not known to pass in either direction between them.
artifacts:
  - research/artifacts/hyperlinear-nonsofic-attack-notebook-2026-08-26.md
---

OPEN.  For the Kun--Thom Theorem E pair `Gamma < G`, let

```text
H = <G, s | s gamma s^(-1) = gamma, gamma in Gamma> = G *_Gamma (Gamma x Z)
  = F(G/Gamma) x| G,
```

the free group on the coset space with `G` permuting the basis.  Claim: `H`
is hyperlinear.

**Payoff.**  `G cap s G s^(-1) = Gamma` by Britton's lemma, so
`<G, sGs^(-1)> = G *_Gamma G = D`, which is nonsofic
(`kt-pair-group-double-is-nonsofic`); hyperlinearity of `H` passes to `D`
and gives the Pestov 3.4 separation (`hyperlinear-nonsofic-from-free-lamp-hnn`).

## Attempts

- **Permanence for semidirect products.**  Alekseev--Bradford
  (arXiv:2601.18742) prove hyperlinearity of `Delta x| G` for hyperlinear
  `Delta`, `G` when the action is a sofic hyperlinear action in their sense;
  `F(G/Gamma)` and `G` are hyperlinear.  The graph's verbatim reading of their
  Corollaries 5.2/5.5 (2026-08-14, `hyperlinear-wreath-model`) is that the
  only stated sufficient condition is soficity of the coset action, which
  Kun--Thom Corollary D refutes (`coordinate-action-not-sofic`, route
  `sofic-action-permanence` dead).  Whether their Definition 4.23 admits
  charts in an auxiliary hyperlinear group that are not permutation models of
  the set is not verified against the source; if it does, the statement to
  prove is that the basis-permuting action is a sofic hyperlinear action
  although the set action is not sofic.  A universal version ("every
  basis-permuting action of a sofic group on a free group qualifies") would
  make the embedded double sofic through the same charts and is false.
- **Constraints.**  Any model represents `Gamma` non-amenably
  (`amenable-kazhdan-models-absorb-compression`) and, on its
  compression-detecting corner, without finite-dimensional or tempered
  subrepresentations; the free lamp lives in the `Gamma`-centralizer with
  the amalgamated-free joint distribution of
  `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`.
- **Fibered orbit models.**  Attach matrix fibers over a finite permutation
  model of `G` and absorb the collisions of cosets forced by compression as
  unitary holonomy controlled by cocycles of the Kazhdan stabilizer; no such
  cocycle with trace-visible holonomy has been produced, and every proposal
  must be checked against the graph's tag/phase obstructions.
