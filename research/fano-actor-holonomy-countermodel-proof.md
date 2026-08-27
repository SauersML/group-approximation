---
rg: 2
id: fano-actor-holonomy-countermodel-proof
kind: route
title: Tensor the Fano Schrodinger packet with the regular representation of its finite actor group
target: fano-moving-packet-retains-actor-holonomy
requires:
  - middle-index-order-seven-orbit-cut-is-native-scale-neutral
  - finite-group-opnorm-support-profile
---

The seven-pair packet acts irreducibly on `H_0`, and the finite binary actor
group `K` is implemented there by `(FMH1)`.  Tensoring with any representation
`sigma` gives `(FMH2)`: packet multiplication is unchanged, actor
multiplication follows from the two representations, and actor conjugation
of packet roots is unchanged because `sigma(k)` commutes with the first
factor.

For `sigma=lambda_K`, an element of order seven acts nontrivially and has
seventh power one.  Restriction of `lambda_K` to any subgroup `L` is
`[K:L]` copies of `lambda_L`; hence every character projection of the finite
center-chain subgroup, including the signed Hecke character, has positive
rank.  Conjugating that projection by `U(t_i) tensor lambda_K(t_i)` produces
the exact seven moving cuts.  Their reservoir transition is the same
`lambda_K(t_i)` at each step and its product is the identity only because it
already has order seven.  This proves the fence.
