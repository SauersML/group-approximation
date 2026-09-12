---
rg: 2
id: fp-self-similar-subgroups-satisfy-pbh-proof
kind: route
title: Zaremsky's envelope is a Rover--Nekrashevych commutator subgroup, hence highly transitive, and BFFHZ Theorem C gives the permutational form
target: fp-self-similar-subgroups-satisfy-permutational-boone-higman
requires:
  - fp-self-similar-groups-embed-in-fp-simple-groups
  - rover-nekrashevych-groups-are-highly-transitive
  - fp-simple-highly-transitive-groups-satisfy-pbh
---

**(a)** Let `G` be a finitely presented self-similar group and `H <= G`.
1. **Envelope.** By Zaremsky's Theorem 1.1, imported as
   `fp-self-similar-groups-embed-in-fp-simple-groups`, `G` embeds in a finitely
   presented simple group. Its proof, read from the extracted PDF text
   (`/scratch.global/sauer354/bh-reviewer/2405.09722.txt`, Section 3):
   - *Re-embedding.* `G` is re-embedded self-similarly in `Aut(T_(d'))`, with
     `d' = md` for an even `m`, through the wreath recursion `σ^⊕m`. This makes
     `V_(d')(G)` have finite abelianization.
   - *The envelope.* "the commutator subgroup [V_d′(G),V_d′(G)] has finite index
     in V_d′(G), hence is finitely presented by Citation 2.3. It is also simple
     by Citation 2.4".
   - *The embedding.* "we finish with embeddings G ↪ (G/H)≀H ↪ [V_d′(G),V_d′(G)]."

   So the envelope is `[V_(d')(G), V_(d')(G)]` for a countable self-similar group.
2. **High transitivity.** That envelope is a nontrivial normal subgroup of a
   Rover--Nekrashevych group of a countable self-similar group. By
   `rover-nekrashevych-groups-are-highly-transitive`, it acts faithfully and
   highly transitively on a countably infinite orbit.
3. **Permutational form.** By BFFHZ Theorem C, (iii) ⟹ (i), imported as
   `fp-simple-highly-transitive-groups-satisfy-pbh`, every subgroup of a
   finitely presented simple highly transitive group satisfies the permutational
   Boone--Higman property. So `H` is in `B_A`.

**(b)** Let `H <= GL_n(K)` be finitely generated, with `K` algebraic over `Q`.
1. **Restriction of scalars.** As in `algebraic-linear-groups-satisfy-boone-higman-proof`,
   the entries of finitely many generators and their inverses generate a number
   field `F` of degree `e` over `Q`. Then `H` embeds in `GL_(ne)(Q)`.
2. **Denominators.** A finitely generated subgroup of `GL_N(Q)` lies in
   `GL_N(Z[1/m])` for some `m`.
3. **Self-similar host.** In his proof of Theorem 1.2, Zaremsky shows that
   `Z[1/m]^N x| GL_N(Z[1/m])` is finitely presented and self-similar, and
   `GL_N(Z[1/m])` is its subgroup fixing `0`.
4. **Conclusion.** By (a), `H` is in `B_A`.

The consequence in the claim is parts 1--3 of
`boone-higman-type-a-class-closed-under-finite-extensions`. ∎
