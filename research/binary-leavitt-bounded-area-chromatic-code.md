---
rg: 2
id: binary-leavitt-bounded-area-chromatic-code
kind: claim
title: Compile the marked Leavitt root into a bounded-area infinite-chromatic commutator code
distinct_from:
  binary-leavitt-three-row-atomic-compiler: that returns three coefficient rows to one prescribed spectral atom and uses the Atomic Leavitt Gap; this bypasses projection decoding and instead asks for a uniformly bounded-area diagonal/off-diagonal commutator code.
  leavitt-steinberg-bounded-area-carmichael-lift: that seeks an order-three Carmichael family for a normalized-Hilbert--Schmidt obstruction; this seeks an operator-norm commutator table whose diagonal entry is the fixed involution z.
artifacts:
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**OPEN.**  In the fixed finite presentation of

```text
Delta=St_20(L_(F_2)(1,2)),             z=x_13(s_1t_1),
```

construct a graph of infinite chromatic number and words `c_v,h_v,a_v`
whose diagonal and edge discrepancies satisfy `(CCC1)--(CCC2)` with constants
independent of `v` and of the edge.

Finite orbit structure or two-transitivity alone is insufficient.  A choice
of an address representative is ambiguous by an element of the point
stabilizer, and commutation with finitely many stabilizer generators gives an
error proportional to the stabilizer word length.  Thus the compiler must
provide either a genuinely bounded-area orbit section or a finite-coordinate
coherence mechanism that does not telescope through an unbounded stabilizer.

Establishing this claim kills `z` by
`infinite-chromatic-commutator-code-kills-mf-mark`; the direct root-saturation
theorem then gives full MF collapse of `Delta`.

## Attempts

* **Two-transitive lamp addresses.**  Same-site and different-site
  commutators give the desired diagonal/off-diagonal table at the group level,
  but different representatives of one address differ by an arbitrary point
  stabilizer element.  Generator-wise lamp covariance then costs the
  stabilizer word length; see
  `stabilizer-generator-control-has-unbounded-address-loss`.
* **Three-transitive addresses.**  Fixing one more point only replaces the
  point stabilizer by a two-point stabilizer.  The same unbounded section
  cocycle remains unless that stabilizer is finite or uniformly exactified.
* **Literal Leavitt prefixes.**  Prefix-free words provide arbitrarily many
  exact orthogonal Heisenberg pairs, but their pair relations occur at
  unbounded presentation area.  This is exact Clifford growth, not a bounded
  compiler.

The next viable attack must construct a bounded-area orbit section directly,
or replace representative coherence by a finite-coordinate selector whose
error does not telescope with address length.
