---
rg: 2
id: simple-kl-via-finite-quotient-certificate
kind: route
title: Separate the cyclic-orbit relators in a finite nonabelian quotient
target: kl-holds-over-two-generator-simple-groups
requires: []
artifacts:
  - research/artifacts/kl-cyclic-orbit-audit-2026-08-24.md
---

Try to find, for every `S`, `m` and `w`, a finite quotient of `N_m` in which
the normal closure of the orbit

    w, alpha(w), ..., alpha^(m-1)(w)

is proper.  Quotienting that finite witness by the orbit normal closure would
produce a nontrivial finite quotient of the canonical group `Q_w`.

This is impossible by `kl-cyclic-orbit-perfect-kernel`, which proves that
`Q_w` has no nontrivial finite quotient.  The same argument rules out a
finite quotient phrased as a proper-normal-closure or normal-rank
certificate: after taking the further quotient by that proper closure, it is
exactly a forbidden finite quotient of `Q_w`.

The failure is specific to **finite** certificates.  It does not prove
`Q_w=1`; it says a proof of `Q_w!=1` must retain a genuinely infinite
quotient.
