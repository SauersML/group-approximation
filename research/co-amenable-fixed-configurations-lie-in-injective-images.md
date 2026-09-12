---
rg: 2
id: co-amenable-fixed-configurations-lie-in-injective-images
kind: claim
title: The image of an injective automaton contains every configuration fixed by a co-amenable subgroup
distinct_from:
  every-injective-ca-preserves-uniform-bernoulli-measure: that asks for invariance of the whole uniform product measure, which is equivalent to the conjecture; this asks only that the configurations constant on the right cosets of one co-amenable subgroup lie in the image, a measure-zero subshift.
  hamming-transports-of-weak-sofic-models-are-soficity: that concerns finite actions supplying charts for every finite set at once; this concerns one infinite coset space and the exact graph automaton it carries, with no separation requirement.
  surjunctive-guard-subgroups-force-surjectivity: that needs the automaton to preserve supports on unions of cosets of a surjunctive guard and concludes surjectivity; this assumes nothing about the automaton and concludes only that the coset-constant configurations are in the image.
artifacts:
  - research/artifacts/subgroup-fixed-configuration-transfer-2026-09-12.md
---

**OPEN.** Let `G` be a group, `A` a finite alphabet, and `H <= G` a co-amenable subgroup, meaning that
`G/H` carries a `G`-invariant mean. Let `tau` be an injective cellular automaton on `A^G`. Then every
configuration constant on the right cosets of `H` lies in `tau(A^G)`.

**Place in the graph.**
- **Implied by the conjecture.**
- **Known cases.** For `H = 1` the hypothesis makes `G` amenable, and the claim is Gromov–Weiss. For
  normal `H` the quotient `G/H` is amenable, and the claim follows from Theorem A(4) of the artifact.
- **Filter.** Garden of Eden patterns of a strict automaton separate two sites of one right `H`-coset,
  for every co-amenable `H` and each of its conjugates.
- **Reach.** Even proved in full, the claim decides surjectivity only when such subgroups separate
  finite sets. Section 3 of the artifact shows that this forces soficity in the repetitive case.

## Attempts

- **Restriction to the Schreier graph (lane w4-free-pos-b, Theorem A of the artifact, proved).**
  - An injective pair acts on the configurations fixed by `H` as graph automata on the labelled
    Schreier graph `H\G`, and the decoder identity survives.
  - So the claim for `H` is exactly surjectivity of one graph automaton with a local left inverse on
    an amenable graph.
  - The counting argument on Følner sets of `H\G` needs the labelled neighbourhood of a missing
    pattern to recur with positive density. Section 2 of the artifact proves the claim under that
    recurrence.
  - Without recurrence it dies: a certificate occurring with zero density along every Følner sequence
    loses to the decoder's boundary factor, as in `decoder-window-fiber-bound-loses-exactly-the-boundary`.
