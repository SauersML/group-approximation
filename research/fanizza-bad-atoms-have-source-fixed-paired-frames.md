---
rg: 2
id: fanizza-bad-atoms-have-source-fixed-paired-frames
kind: claim
title: Every Fanizza bad atom has a source-fixed full-center paired frame
artifacts:
  - experiments/fanizza_atom_paired_frame_search.py
distinct_from:
  support-packet-paired-word-frame-exposes-forbidden-rank: that finds the special 101-to-011 chart in the order-128 support packet; this constructs a chart for every bad atom of all three actual Fanizza predicate packets.
  every-forbidden-atom-has-fixed-schur-pauli-words: that names only the relative pair; this adjoins one baseline pair and proves the plus/minus edge groups are isomorphic while fixing the entire source selector center.
  two-center-paired-frames-cannot-isolate-the-joint-hot-bit: that proves two commutator coordinates are insufficient; the frames here use a baseline coordinate but their symbolic center still has rank four, not the desired rank three.
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

The BCS selector atom is not shuffled: the rank-two target retains its source
character exactly.  This solves the **source-atom preservation** part of the
finite search.

It does not solve the partial-center interface.  The coefficient commutator
map of every witness has kernel dimension two and hence image rank four.  By
contrast, the canonical support/E5 frame has kernel dimension three and image
rank three.  Kernel dimension is invariant under every change of the four
frame generators, so no `GL_4(F_2)` word change can identify these frames with
the support/E5 chart.  Transporting their entire coefficient center therefore
falls under `full-center-hnn-transport-cancels-schur-multiplicity`.

The finite audit exhausts every coordinate core pivot and every coefficient
character.  It verifies all five properties by exact binary linear algebra
and succeeds on `26/26` bad atoms.  It also computes the common rank-four
kernel, compares it with the rank-three support kernel, and exhausts all
`20160` invertible four-generator word changes; none carries one kernel to the
other.  The largest run uses one low-priority core, under 15 MB, and no
scheduler job.

Thus the coordinate-pivot ansatz closes one finite subproblem and exposes the
next one sharply: find a source-fixed frame whose symbolic commutator image
has rank three, or prove that arbitrary dual baseline words cannot reduce the
rank-four image.  Only such a rank-three chart could feed the one-sided E5
valuation reservoir without transporting the full center.
