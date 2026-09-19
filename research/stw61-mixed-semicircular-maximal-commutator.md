---
rg: 2
id: stw61-mixed-semicircular-maximal-commutator
kind: claim
title: Mixed semicircular unitaries force maximal commutators beyond every proper Toeplitz coefficient corner
distinct_from:
  stw61-mf-coefficient-maximal-commutator: This uses the actual Toeplitz isometries with a surviving nonzero defect, rather than a matrix-quotient coefficient representation, and controls a specified mixed generated algebra.
artifacts:
  - research/artifacts/stw61-mixed-semicircular-defect-complete-obstruction-2026-09-05.md
---

In the full unital free product C=C(S1)*T2, let z be the circle
unitary, let s1,s2 be the Toeplitz isometries, and put

```text
p=s1 s1*,  p2=s2 s2*,  e=1-p-p2,
h_i=z s_i+s_i* z*,  H=C*(1,h_1,h_2).
```

Then ||[z,WpW*]||=1 for every W in U(H).

For every real t!=0, the explicit conjugate
q_t=exp(i t h_1)p exp(-i t h_1) is contained in no proper
Toeplitz coefficient projection, nor in any f(z)-conjugate of
one for a scalar continuous unitary function f on S1. All three
compressions e q_t e, p q_t p, and p2 q_t p2 are nonzero.
Both q_t and 1-q_t are properly infinite and full.

Thus this obstruction applies to a concrete family escaping the
fixed proper coefficient corners. It does not identify H with
the entire free product or treat every unitary of C. Full-free-
product inclusion transfers the stated norm result to C*(v,T2)
inside A*T2 for any full-spectrum unitary v in A. LXI remains open.

ROUTES

stw61-left-right-fock-commutator-proof
