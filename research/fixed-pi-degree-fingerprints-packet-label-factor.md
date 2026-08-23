---
rg: 2
id: fixed-pi-degree-fingerprints-packet-label-factor
kind: claim
title: A fixed polynomial-identity degree fingerprints the packet label factor across the rectangular escape
artifacts:
  - research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md
distinct_from:
  two-generator-amitsur-levitzki-dimension-oracle: that enumerates an unbounded family whose index tracks the unknown ambient matrix dimension; this uses one fixed small standard polynomial to distinguish two fixed packet degrees.
  multiplicity-pi-turing-tape: that treats the arbitrary commutant multiplicity M_k as a dimension-sensitive tape; this is amplification-blind and fingerprints the finite label factor M_r against a forced M_(r^2) target.
  paired-same-reservoir-boundary-lemma: that asks for literal common-reservoir closure or a leakage payment; this asks only that one fixed polynomial evaluation be transported from the source packet to a full transverse target factor.
---

For one fixed packet degree `r>=2`, choose a fixed unitary tuple

```text
Y=(Y_1,...,Y_(2r)) in U(r^2)^(2r)
```

with

```text
kappa_r=||s_(2r)(Y)||_(2,r^2)>0,
```

where `s_(2r)` is the alternating standard polynomial.  In every sufficiently
accurate microstate of the selected affine/atlas compressor cell, there is a
projection `P` of trace at least a fixed `alpha>0` and transported word tuples
`X^(n),Y^(n)` on `P` such that:

1. the source finite packet places `X^(n)` within `o(1)` of
   `M_r tensor I`, hence `||s_(2r)(X^(n))||_2=o(1)` by
   Amitsur--Levitzki;
2. the closed-cycle transport relations give
   `||s_(2r)(X^(n))-s_(2r)(Y^(n))||_2=o(1)`; and
3. the transverse target packet places `Y^(n)` within `o(1)` of copies of
   the fixed full `M_(r^2)` tuple `Y`, hence
   `||s_(2r)(Y^(n))||_2 >= sqrt(alpha) kappa_r-o(1)`.

These conclusions are incompatible.  The point is that tensoring either
packet with arbitrary external multiplicity leaves both PI evaluations
unchanged, so the exact `rectangular-escape` cannot repair the discrepancy by
trading label degree for spectator multiplicity.

## Attempts

- **Do not assume the target is full.** An `M_r` subfactor embeds in
  `M_(r^2)`, and on such a retreat the standard polynomial still vanishes.
  The load-bearing statement is that fixed transverse packet words generate
  the full target factor on positive trace; mere target dimension is useless.
- **A common spectator is harmless.**  Tensoring both named tuples and their
  carrier by an arbitrary identity factor preserves every normalized PI
  evaluation.  Therefore the scalar spectator no-go does not force mutual
  bicommutant extraction here.  The direct route
  `nonhyperlinear-directly-from-fixed-pi-fingerprint` uses only the three
  displayed PI conclusions of this claim.  What remains hard is making the
  full transverse tuple and its transport word-visible on the same carrier,
  not eliminating an anonymous common tensor factor.
- **Addition is analytic, not a relator.** The signed sum defining
  `s_(2r)` is formed in the proof from finitely many word evaluations.  No
  group-ring addition compiler is needed, but every monomial must have a
  bounded transport estimate.
- **Native Fanizza restriction.** The refuted global identity
  `Xtilde Ztilde Xtilde Ztilde=J` cannot supply the transport: the phase turns
  off at the terminal cell.  Any Fanizza instantiation must use the surviving
  one-triangle incidence and terminal guard, not the dead three-bit
  recurrence.
- **Fast kill test.** Evaluate `s_(2r)` on candidate target tuples inside the
  exact rectangular model.  If all word-forced tuples are conjugate into an
  `M_r tensor I` subfactor, this route is blind and should be closed.
