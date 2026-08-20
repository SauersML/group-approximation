---
rg: 2
id: fanizza-bad-atoms-have-source-fixed-paired-frames
kind: claim
title: Every Fanizza bad atom has a source-fixed three-coordinate paired frame
artifacts:
  - experiments/fanizza_atom_paired_frame_search.py
distinct_from:
  support-packet-paired-word-frame-exposes-forbidden-rank: that finds the special 101-to-011 chart in the order-128 support packet; this constructs a chart for every bad atom of all three actual Fanizza predicate packets.
  every-forbidden-atom-has-fixed-schur-pauli-words: that names only the relative pair; this adjoins one baseline pair and proves the plus/minus edge groups are isomorphic while fixing the entire source selector center.
  two-center-paired-frames-cannot-isolate-the-joint-hot-bit: that proves two commutator coordinates are insufficient; this uses the minimal repair, one additional baseline coordinate.
---

For each of the 26 bad atoms in the three nonlinear Fanizza predicate shapes,
there is an explicit four-generator paired frame with the following
properties.

1. Constant row and column word changes put the atom's Schur matrix in identity
   form while retaining the last coordinate as the named Schur pair from
   `(SPW3)`.
2. One of the baseline identity pivots is retained as a core Pauli pair.
3. On the coefficient copy, the minus frame uses the identity words and the
   plus frame uses

```text
p_core -> p_core p_rel,   p_rel -> p_rel,
q_core -> q_core q_rel,   q_rel -> q_rel.             (SFF1)
```

4. The coefficient commutator maps of the plus and minus frames have the same
   relation kernel.  Therefore the induced edge-group isomorphism extends by
   the identity on the **entire source selector center**.
5. At source atom `a`, the stationary minus character `(a,a)` has alternating
   rank zero.  A listed plus coefficient character has rank two, and its
   induced minus frame has a rank-two target whose source character is still
   exactly `a`.

Thus the only exported datum is one coefficient-side reverse Pauli bit; the
BCS selector atom itself is not shuffled.  Literal reuse of the source center
across the three contexts therefore gives exact shared endpoint marginals,
while the reverse coefficient character can be attached to the one-sided E5
valuation reservoir.

The finite audit exhausts every core pivot and every coefficient character.
It verifies all five properties by exact binary linear algebra and succeeds on
`26/26` bad atoms.  The largest run uses one low-priority core, under 15 MB,
and no scheduler job.

This closes the finite partial-center chart problem for the actual Fanizza
menu.  It does not yet prove that the three HNN copies and the E5 degree clock
retain their baseline carrier with polynomial total defect; that global
one-sided return is still required.
