---
rg: 2
id: invariant-bs-block-cut-leaves-a-passive-coordinate-basin
kind: claim
title: Cutting the sublinear invariant BS hull leaves only the passive moving-level coordinate basin
distinct_from:
  regular-short-low-frequency-bs-source-hull-is-sublinear: that constructs the invariant hull and proves its density vanishes; this asks to split the physical involution across it and identify the analytic problem on the complement.
  bs14-thresholded-newton-needs-coordinate-basin: that states the global high/low residual threshold problem before an integrable active carrier has been built; this starts after the active source and both exits lie in one invariant subcore.
  low-rank-reflection-surgery-preserves-the-exact-bs-core: that controls a non-invariant finite-rank reflection change; this asks for a block decomposition by the new invariant hull and a basin theorem on its passive complement.
  sublinear-bs-block-surgery-is-invisible-to-relative-liftability: that proves the proposed block cut, polarization, and exact active-block replacement leave the relative ultraproduct lifting class unchanged; this remains the open coordinate lift on the passive representative.
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

One tempting change of coordinates is now ruled out sharply.
`sl2-half-rational-h2-refutes-torsion-normalized-op-basin` computes
`H^2(PSL_2(Z[1/2]),Q)=Q` from the one-edge amalgam and applies Dadarlat's
matricial-stability obstruction.  Nearest-root normalization works in
operator norm, so there are exact Iwahori torsion frames with structural
defect tending to zero which stay outside every strict global
operator-norm endpoint basin.  Thus exactifying the two triangles first and
then invoking the tangent gap cannot prove item 4.  This does not refute the
claim as stated: the surviving hypothesis is precisely the opposite normal
form, with the BS core and inversion exact, together with flexible
`o(d)` repair after the active cut.

Full regular-quotient padding does not solve the `Q_n` block uniformly:
`congruence-regular-padding-is-conductor-not-low-rank` proves both the
restriction-lattice firewall and the rank-one Weil dimension blowup.  The
small block must be changed to an efficient native endpoint cell; it cannot
be swallowed by a whole regular congruence packet.

There is no contradiction/ultraproduct shortcut from items 1--3 to item 4.
`sublinear-bs-block-surgery-is-invisible-to-relative-liftability` proves
that the entire block cut and arbitrary exact replacement of `Q_n` change
the tuple by `o(1)` in flexible normalized HS.  The original and passive
tuples therefore define the same exact relative ultraproduct homomorphism,
and one is flexibly liftable by coordinate congruence endpoints exactly
when the other is.  Exact order-three rounding of

```text
A=X S^2,       B=X R S,       B=A(S^(-2)RS)
```

also remains inside that same ultraproduct class and does not preserve the
fixed relative product at the coordinates.  Hence even granting that the
active hull captures every high singular carrier, block cutting merely
produces a cleaner representative of the already isolated relative-lift
problem.  A proof of item 4 must add a coordinate arithmetic or relative
semiprojectivity theorem; it cannot follow from ultraproduct exactness or
the tangent quotient alone.
