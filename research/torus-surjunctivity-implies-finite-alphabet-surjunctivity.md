---
rg: 2
id: torus-surjunctivity-implies-finite-alphabet-surjunctivity
kind: claim
title: A group over which every injective torus-alphabet automaton is surjective is surjunctive on every finite-alphabet full shift
distinct_from:
  gottschalk-surjunctivity-conjecture: that is the finite-alphabet conclusion alone; this is only the implication from torus-alphabet surjunctivity, which fails over a group only if that group is torus-surjunctive and not finite-alphabet surjunctive.
  stable-finiteness-forces-binary-surjunctivity: that transfers from linear algebra over F_2; this would transfer from a topological statement whose linear shadow is characteristic zero.
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

For every countable group `G`, suppose that for every `d >= 1` every injective continuous
`G`-equivariant self-map of `(T^d)^G` is surjective. Then every injective cellular
automaton on every finite-alphabet full shift `A^G` is surjective.

This is the transfer step of `gottschalk-via-torus-alphabet-degree-transfer`. No mechanism
is known. It fails over `G` exactly when `G` is torus-surjunctive but carries a strict
finite-alphabet automaton.

## Attempts

- 2026-09-17 (swarm-0917-w4-gs-decomp-new): artifact Section 3.2. Obstructions to every
  mechanism that uses equivariant maps between the two shifts.
  - **(O1) No factor maps.** `(T^d)^G` is connected, so every continuous map from it to
    `A^G` is constant.
  - **(O2) Subsystem embeddings prove nothing.** Suppose `iota: A^G -> (T^d)^G`, e.g.
    `(Z/n)^G = ker[n] in T^G`, intertwines `tau` with an injective torus automaton
    `sigma`.
    - Torus surjunctivity only makes `sigma` a homeomorphism.
    - A homeomorphism may map `iota(A^G)` strictly into itself.
    - Excluding that is the Gottschalk statement for `tau` itself.
  - **(O3) Mixed alphabets reintroduce counting.** On `A x T^d`, degree acts only inside
    components of window spaces. The component count is the finite-alphabet problem.
  - **What a proof would need.** A non-equivariant construction turning a strict datum
    into an injective torus automaton with singular degree matrix. It must transport
    information from characteristic `p` to characteristic `0`, because linear torus
    surjunctivity holds for every group (Kaplansky), while linear finite-alphabet
    surjunctivity is stable finiteness of `F_p[G]` and is open. That gap is the reason to
    expect this step to be deep or false.
