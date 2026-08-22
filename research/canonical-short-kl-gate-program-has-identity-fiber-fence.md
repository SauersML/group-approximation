---
rg: 2
id: canonical-short-kl-gate-program-has-identity-fiber-fence
kind: claim
title: Every canonical one-KL-gate short word is blocked by the identity fiber
distinct_from:
  kl-gate-times-pure-root-has-identity-fiber-obstruction: that treats products with the two cyclic pure-root types; this adds coordinate-cycle monomials and the shortest nontrivial commutators.
  two-kl-gate-orbit-has-identity-fiber-obstruction: that treats two copies of the mixed gate; this fences the remaining canonical one-gate generator words.
  inverse-packet-conjugator-must-mix-s-and-t-charts: that is a broad necessary condition; this is an exact coefficient obstruction for a finite canonical mixed-word atlas.
artifacts:
  - research/artifacts/kl-gate-in-c3-corner-chart-2026-08-21.md
  - research/artifacts/verify-kl-gate-c3-corner.py
---

For every coordinate KL gate `q_i` and nontrivial coordinate-cycle power
`phat^j`, both `q_i phat^j` and `phat^j q_i` have packet-correction identity
bits `(0,0,0)` against the base bit one.  This rejects all 760 words.

For the cyclic roots `a_j=x_12(s_0)^(phat^j)` and
`f_j=x_12(t_1)^(phat^j)`, exactly 80 of the 400 commutators in each of
`[q_i,a_j]` and `[q_i,f_j]` are nontrivial.  Every nontrivial commutator has
the same `(0,0,0)` correction triple and therefore an odd identity fiber.
Together with the preceding single-gate, two-gate, and gate/root product
audits, this exhausts the canonical one-KL-gate short-word program.

The fence is deliberately finite: arbitrary noncyclic prefix permutations
and longer nested Steinberg words are not covered.
