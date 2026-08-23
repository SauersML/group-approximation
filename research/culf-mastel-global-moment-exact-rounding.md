---
rg: 2
id: culf-mastel-global-moment-exact-rounding
kind: claim
title: Culf--Mastel assignment-to-context rounding preserves every global-variable moment exactly
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
distinct_from:
  culf-mastel-oracular-2csp-perfect-gap-family: that records the resulting machine-indexed gap family; this extracts a stronger invariant from the trace-dependent rounding inside Lemma 3.10.
  mastel-slofstra-private-context-augmentation-preserves-defect: that adds private variables by classical weighted homomorphisms; this rebuilds context PVMs inside one trace while leaving all global assignment operators untouched.
  pointed-weighted-defect-gap-pulls-back: that is a general homomorphism lemma; this also covers the trace-dependent construction which is not a fixed homomorphism.
---

In the proof of Culf--Mastel Lemma 3.10, let `tau=rho o phi` be the input
trace on the assignment-with-commutation algebra.  Their output
representation `chi` rebuilds the context PVMs but satisfies, for every
global assignment variable `x`,

```text
chi(sigma'(x))=phi(x).                                  (GMR1)
```

Consequently the output trace `tau'` obeys

```text
tau'(p)=tau(p)                                           (GMR2)
```

for every noncommutative star polynomial `p` in the global variables, while

```text
def(tau') <= poly(k^L) def(tau).                         (GMR3)
```

The rebuilt operators lie in the same tracial von Neumann algebra as the
input.  In particular, Connes embeddability of the input trace implies
Connes embeddability of the output trace.  Therefore `(GMR2)--(GMR3)` also
transport every pointed defect gap whose witness belongs to the global
assignment algebra.

