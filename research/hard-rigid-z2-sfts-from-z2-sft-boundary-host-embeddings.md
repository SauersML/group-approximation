---
rg: 2
id: hard-rigid-z2-sfts-from-z2-sft-boundary-host-embeddings
kind: route
title: Feed the complexity-diagonal group of the hard-language theorem into the boundary-product embedding and read off a hard rigid SFT
target: hard-quantum-rigid-free-minimal-z2-sfts-exist
requires:
  - decidable-algebras-embed-in-z2-sft-boundary-product-hosts
  - z2-sft-boundary-hosts-need-unboundedly-hard-sft-languages
---

Let `T` be recursive.

1. By `z2-sft-boundary-hosts-need-unboundedly-hard-sft-languages`, there is a
   two-generated group `H` with solvable word problem such that `F_2[H]` embeds
   injectively in `B_Ω ⊗ L_∂(d)` for no `T`-decidable `Z^2`-SFT `Ω` and no
   `d >= 1`. The embedding may be unital or not.
2. By `decidable-algebras-embed-in-z2-sft-boundary-product-hosts`, applied to
   `H`, there are:
   - a free minimal `Z^2`-SFT `Ω` over `F_2` with `B_Ω` finitely presented;
   - some `d >= 2`;
   - a unital embedding `F_2[H] -> B_Ω ⊗ L_∂(d)`.
3. By step 1, this `Ω` is not `T`-decidable. So `Ω` witnesses the statement for
   `T`. `∎`

**Contrapositive.** Suppose there is a recursive `T` such that every free
minimal `Z^2`-SFT with finitely presented binary crossed product is
`T`-decidable. Then `decidable-algebras-embed-in-z2-sft-boundary-product-hosts`
is false, and the group `H` of step 1 for that `T` is a counterexample.
