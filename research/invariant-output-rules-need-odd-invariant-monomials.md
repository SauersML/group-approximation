---
rg: 2
id: invariant-output-rules-need-odd-invariant-monomials
kind: claim
title: Over F_2 an injective automaton with involution-invariant output needs a nonzero linear part and an odd number of invariant monomials
distinct_from:
  invariant-output-automata-have-only-nonlinear-decoders: that forbids linear decoders through augmentation; this constrains the encoder's own normal form, a nonzero even linear part plus an odd number of relabeling-invariant monomials of degree at least two, and kills norm rules.
  linear-invariant-output-automata-fail-augmentation: that classifies the linear encoders; this is a necessary condition on every nonlinear encoder of the same shape.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `G` be any group, `H` a finite subgroup of even order, `h in H` an
involution, and `tau` an injective automaton on `F_2^G` with output invariant under
`H`. Write the local rule in algebraic normal form,
`f = c + sum_m a_m x_m + (higher monomials)`. Then:

1. `a != 0`, and `a_(hm) = a_m`, so the linear support has even size;
2. the number of monomials invariant under the relabeling `m -> hm` is odd, and
   each has degree at least two;
3. a norm rule, all of whose monomials are products over unions of orbits
   `{m, hm}`, is never injective.

(1) is `tau(e_1) != tau(0)`. (2) is that `tau` permutes the two constant
configurations, together with the pairing of non-invariant monomials under
relabeling. (3) follows from (1). Proof: Section 3 of the artifact.
