---
rg: 2
id: invariant-bs-block-cut-leaves-a-passive-coordinate-basin
kind: claim
title: Cutting the sublinear invariant BS hull leaves only the passive moving-level coordinate basin
distinct_from:
  regular-short-low-frequency-bs-source-hull-is-sublinear: that constructs the invariant hull and proves its density vanishes; this asks to split the physical involution across it and identify the analytic problem on the complement.
  bs14-thresholded-newton-needs-coordinate-basin: that states the global high/low residual threshold problem before an integrable active carrier has been built; this starts after the active source and both exits lie in one invariant subcore.
  low-rank-reflection-surgery-preserves-the-exact-bs-core: that controls a non-invariant finite-rank reflection change; this asks for a block decomposition by the new invariant hull and a basin theorem on its passive complement.
---

**OPEN; UPDATED TERMINAL REGULAR-FACE GATE.**  Let `Q_n` be the
`o(d_n)`-rank `(R_n,S_n)`-invariant hull supplied by
`regular-short-low-frequency-bs-source-hull-is-sublinear`, enlarged by the
two active exit ranges and the finite-rank Gram-surgery support.  Put
`P_n=1-Q_n`.

Block-cut the supplied reflection across `Q_n (+) P_n`, polarize the two
selfadjoint compressions, and replace the entire `Q_n` block by any exact
finite endpoint, allowing `o(d_n)` padding.  Prove that the `P_n` block has

1. the exact restricted BS core;
2. exact involution and inversion after an `o(1)` normalized-HS change;
3. both cubic residuals tending to zero in operator norm; and
4. operator-norm distance tending to zero from the **union** of exact
   moving-level congruence endpoint orbits over that restricted core.

The first item is automatic because `Q_n` reduces the core.  Block cutting,
polarization, and `low-rank-reflection-surgery-preserves-the-exact-bs-core`
pay every new fixed-word error by `o(d_n)` rank.  The source construction is
designed so that all high cubic carriers are placed in `Q_n`; what remains
to prove is that no high singular direction is lost in the source/exit
decoder and that the passive operator-small tuple satisfies item 4.

Item 4 is exactly the coordinate-basin hypothesis needed by the uniform
tangent gap.  Block cutting supplies an integrable active modification, but
small operator-norm residual values still do not formally imply proximity
to a zero of a nonlinear word map.  A proof must use the moving congruence
endpoint union, not a preselected regular orbit.

Full regular-quotient padding does not solve the `Q_n` block uniformly:
`congruence-regular-padding-is-conductor-not-low-rank` proves both the
restriction-lattice firewall and the rank-one Weil dimension blowup.  The
small block must be changed to an efficient native endpoint cell; it cannot
be swallowed by a whole regular congruence packet.
