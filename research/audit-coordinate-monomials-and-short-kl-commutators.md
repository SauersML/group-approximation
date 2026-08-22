---
rg: 2
id: audit-coordinate-monomials-and-short-kl-commutators
kind: route
title: Audit coordinate-cycle products and the shortest KL commutators
target: canonical-short-kl-gate-program-has-identity-fiber-fence
requires:
  - kl-gate-times-pure-root-has-identity-fiber-obstruction
  - two-kl-gate-orbit-has-identity-fiber-obstruction
  - kl-gate-corner-test-is-an-even-unit-fiber-audit
artifacts:
  - research/artifacts/kl-gate-in-c3-corner-chart-2026-08-21.md
  - research/artifacts/verify-kl-gate-c3-corner.py
---

Use explicit inverses for `q_i phat^j` and `phat^j q_i`, and reverse the four
involutions in each commutator.  Expand only the identity fiber of the two
linear and one bilinear packet corrections in Bergman normal form.  All
correction triples vanish.  Canonicalizing the commutator word itself leaves
80 nontrivial words in each root-type grid; these are therefore genuine new
negative cases rather than repetitions of the base defect.
