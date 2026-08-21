---
rg: 2
id: bounded-template-average-blr-occurrence-decoder
kind: claim
title: Recover average dense BLR energy from bounded-template occurrences
distinct_from:
  bounded-template-all-pairs-additive-decoder: that asks for an all-pairs almost-action; polar BLR self-correction now reduces it to this strictly weaker average-energy interface.
---

OPEN.  Construct a bounded-degree, bounded-template, perfect-completeness
same-basis occurrence test whose defect `epsilon` decodes, on one common
positive-mass carrier, a unitary table `f:F_2^n->U(d)` satisfying

```text
E_(x,y)||f(x)f(y)-f(x+y)||_2^2 <=omega(epsilon),              (BTA1)
```

with `omega(epsilon)->0` independent of `n,d`.  Average change from the tested
occurrences to the decoded table must obey the same kind of modulus.  No
pointwise or maximum-over-pairs conclusion is required.

The remaining issue is incidence/noncontextual agreement, not finite-group
stability: `unitary-blr-average-self-corrects-uniformly` upgrades `(BTA1)` to
the uniform almost-action required downstream, and abelian HS stability then
rounds in the same dimension.

## Attempts

- A direct candidate is a bounded-degree subset of the projective-line BLR
  checks `{x,y,x+y}` whose parity-check kernel is the binary simplex code and
  whose syndrome expands distance to that code.  Scalar LDPC soundness is not
  enough: arbitrary reflection solutions form the nonabelian solution group
  of the sparse parity system, so an operator/noncontextual soundness theorem
  is still required.
- Dense BLR plus equality fibers controls an average representative, but a
  fixed mixed-test port can be corrupted at cost `O(1/m)` in a fiber of size
  `m`.  Sampling the mixed edge uniformly over the fiber requires many lifts
  of the same logical pair, recreating the two-pair contour.  This quantitative
  rooted-port obstruction is recorded in the parent decoder claim.

