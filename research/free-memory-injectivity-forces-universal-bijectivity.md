---
rg: 2
id: free-memory-injectivity-forces-universal-bijectivity
kind: claim
title: An encoder injective over a surjunctive cover of its memory group is bijective over every compatible image
distinct_from:
  forward-memory-lifts-exclude-strict-cellular-sections: that lifts a given decoder's forward rectangle injectively to a surjunctive cover; this assumes only that the encoder is injective over some surjunctive cover, needs no decoder, and pushes the cover's own inverse down to every compatible image.
  triangular-forward-tables-force-surjectivity: that proves bijectivity when a decoder's minimal forward partition peels to a free table group; this needs no decoder and applies whenever the encoder alone is injective over the free group on its memory letters.
  bijective-designs-force-every-finite-presentation: that forces any presentation through a decoder's shared addresses while the encoder stays injective over the free group; this shows such encoders are always bijective, so a counterexample's encoder needs relations for injectivity itself.
artifacts:
  - research/artifacts/bijective-forcing-of-table-cores-2026-09-12.md
---

**ESTABLISHED** by `free-memory-injectivity-bijectivity-proof`.

**Theorem.** Let `mu : A^M -> A` be a rule on formal memory addresses.
- Let `H` be a surjunctive group, with a realization `rho_H` of `M` over which the
  encoder is injective.
- Let `rho_G` realize `M` in a group `G`, and suppose some homomorphism
  `phi : <rho_H(M)> -> G` satisfies `phi o rho_H = rho_G`.

Then the encoder over `G` is bijective.

**Corollary (free memory).** If `mu` is injective over the free group on its non-identity
memory letters, then it is bijective over every group and every realization.

**Corollary (counterexamples).** The encoder of any strict pair over `G` fails to be
injective over:
- the free group on its memory letters;
- every residually finite, amenable or sofic cover of its memory group admitting a
  compatible homomorphism.

So a counterexample needs nonsofic relations already for injectivity, not only for the
failure of surjectivity.

**Consequences for designs.** The relators forced by
`bijective-designs-force-every-finite-presentation` come from a decoder's choice of shared
addresses. Its encoder is injective over the free group, so the corollary recovers its
bijectivity. A strict design must use an encoder that is not injective over any
surjunctive cover of its memory group.

Proof: Section 7 of the artifact.
