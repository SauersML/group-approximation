---
rg: 2
id: kl-gate-corner-test-is-an-even-unit-fiber-audit
kind: claim
title: Testing the KL gate in the corner is an even-fiber audit of a bounded unit multiset
distinct_from:
  canonical-left-comb-kl-gate-is-a-mixed-involution: that constructs the candidate; this identifies the exact finite certificate deciding whether it solves the corner equation.
  leavitt-length-six-three-gate-weight-survivor: that uses moved vectors to distinguish single group words; this explains why applying the total group-algebra defect to the same module is necessarily blind.
  both-rank-three-factors-must-be-packet-corrected: that derives the abstract two-packet equation; this specializes it to the KL involution and turns it into a bounded equality partition.
artifacts:
  - research/artifacts/kl-gate-in-c3-corner-chart-2026-08-21.md
  - research/artifacts/verify-kl-gate-c3-corner.py
---

Let `P=e[qhat]k[qhat]e` for the canonical transported KL involution.  It
solves the inverse-pair ansatz exactly when

```text
A P + P B + P^2+Delta=0.
```

After expansion this is equivalent to every unit of `R^x` occurring with
even multiplicity in one fixed finite multiset.  Applying the total sum to a
Leavitt module cannot decide it: evaluation kills `k` and sends the whole
expression to zero identically.  A valid positive certificate must pair all
terms as equal units; a valid negative certificate must distinguish at least
one odd term from every other term by prefix normal form.  Exact Bergman
normal form rejects all twenty coordinate-cycle conjugates: every residue has
between `122` and `234` odd unit fibers.  It also rejects all `380`
transported coefficient-one roots `x_ij(1)`, whose residues have `122`, `168`,
or `176` odd fibers.  In all 400 cases the identity unit is itself an odd
fiber, giving a uniform explicit separating certificate.

## Attempts

Normalizer, pure-chart, and relative-free projection do not reject `qhat`.
The existing KL moved-vector script tests equality of individual group words,
not parity fibers of this expanded group-algebra element, so it cannot be
reused on the total sum.  The separate exact verifier canonicalizes every
unit before collecting fibers and supplies the negative certificates above.
