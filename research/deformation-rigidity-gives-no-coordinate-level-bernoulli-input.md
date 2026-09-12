---
rg: 2
id: deformation-rigidity-gives-no-coordinate-level-bernoulli-input
kind: claim
title: Popa's deformation/rigidity theory gives no coordinate-level input forcing injective automata to preserve Bernoulli measure
distinct_from:
  compressed-coset-shifts-carry-strict-equivariant-embeddings: that constructs the strict continuous equivariant injection of a compressed coset shift; this uses it to show that s-malleability and weak mixing on a Kazhdan subgroup, the hypotheses of cocycle superrigidity, coexist with strict injections, and adds the singularity, factor-map and finite-fibre facts.
  kazhdan-bernoulli-rigidity-forces-surjective-embeddings: that is the refuted architecture "rigid Bernoulli dynamics admit no strict self-embeddings"; this is a theorem naming which tools of Popa's theory fail and why each one carries no information about cylinder masses of a strict image.
  measure-conjugacy-invariants-cannot-certify-surjectivity: that is the general principle that every measure-conjugacy invariant agrees on mu and a strict image measure; this is specific to Popa's theory, where the malleable deformation is a coordinate-level, non-invariant tool, and names why that tool too carries no cylinder information (singular images, coset calibration of the superrigidity hypotheses, measure-preserving XOR factors).
artifacts:
  - research/artifacts/popa-deformation-rigidity-and-bernoulli-preservation-2026-09-12.md
---

Let `G` be a group, `A` a finite alphabet, `mu` the uniform product measure on
`A^G`, `tau` an injective cellular automaton and `nu = tau_* mu`.

1. **Singularity.** If `tau` is strict, `nu` is singular to `mu`, and the graph
   joining `(id x tau)_* mu` is singular to `mu x mu`. Popa's s-malleable
   deformation acts only on measures absolutely continuous to `mu x mu`, so it
   never acts on measures carrying the window laws of `nu`. Transported
   through `tau`, it becomes a conjugacy invariant with no cylinder data.
2. **Coset calibration.** Over `G = R^x` with `H = V_1` and the compressor `u` of
   `compressed-coset-shifts-carry-strict-equivariant-embeddings`, the product
   shift `G ↷ ([0,1]^(G/H), Leb)` is s-malleable and weakly mixing on the
   Kazhdan group `G`. These are the hypotheses of Popa's cocycle superrigidity
   theorem. Yet `y -> y o psi_u` is a continuous equivariant injection pushing
   the product measure onto a null set. So no argument from those hypotheses
   alone proves that continuous equivariant injections of product shifts
   preserve product measure. Freeness of the index set enters Popa's theory
   only through orbit-equivalence and W*-superrigidity, whose conclusions are
   conjugacy invariants shared by `mu` and `nu`.
3. **Factor maps.** If `G` has an element `s` of infinite order,
   `x -> (x(g) + x(gs))_g` over `Z/2` is a non-injective cellular automaton that
   preserves `mu`. So rigidity cannot upgrade a measure-preserving finite-memory
   decoder to an injective map.
Finite-to-one extensions and flip lifts, where superrigidity does apply, belong
to the sibling lane `gk-p-inf-kazhdan`
(`kazhdan-map-bernoulli-finite-extensions-are-trivial`,
`strict-pair-flip-lifts-are-relatively-weakly-mixing`). Neither gives more
than invariant sections, which every strict pair already has.

Consequently a positive proof of
`injective-cas-over-leavitt-units-preserve-uniform-bernoulli`, or of
`every-injective-ca-preserves-uniform-bernoulli-measure`, must produce a
coordinate-level identity such as the window balance, using locality over the
free regular index set. Popa's theory supplies none.

Items 1–3 are proved in Sections 0–3 of the artifact from definitions and
elementary arguments. None uses the truth of Popa's theorem, only its
hypotheses. The general principle that measure-conjugacy
invariants cannot certify surjectivity is the sibling lane
`gk-p-bernoulli-ergodic`'s node `measure-conjugacy-invariants-cannot-certify-surjectivity`.
