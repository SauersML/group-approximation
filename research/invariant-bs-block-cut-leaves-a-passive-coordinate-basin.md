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

Even the complete active residual polar datum does not choose that point of
the union.  `active-residuals-do-not-name-passive-endpoint` constructs two
tuples with the same exact core and literally identical nonzero active
residual operators, but with macroscopically separated passive exact
involutions.  The same active cell completes both after restoring one line.
Consequently item 4 must use the compressed passive involution itself; it
cannot be a function only of the core, the active hull, or its principal-
angle and singular-value ledgers.

The strongest unconditional positive endpoint is coordinatewise.
`fixed-core-passive-fiber-has-positive-basin` defines, for every fixed
passive core `beta` and target distance `eta`, a positive compactness radius
`delta_beta(eta)` below which the two cubic residuals force proximity to
the simultaneous finite endpoint fiber over `beta`.  Therefore a
triangular active/passive repair closes whenever the post-surgery passive
residual lies below its own coordinate radius.  What is missing in item 4
is exactly the uniform moving-core comparison needed to guarantee this;
finite-dimensional compactness supplies no lower bound on those radii.

The natural spectral-truncation contradiction is also fenced quantitatively.
`moving-basin-blowup-needs-displacement-charge` shows that if the passive
reflection remains distance `eta` from every endpoint, then for every
`tau<eta` its displacement from every endpoint has an operator-`>tau`
spectral part of relative rank at least `(eta^2-tau^2)/4`.  Thus the
operator-large motion costs positive-density padding, not the available
`o(d)` active budget.  Relator-energy thresholds control residual carriers,
not these unknown endpoint-displacement carriers.  Connecting the two by a
rank estimate would already prove item 4.  Uniform tangent gaps at exact
zeros cannot supply that global estimate.

Even legal invariantization of a canonical displacement projection has an
unbounded packet loss.  `displacement-carrier-has-p-fold-bs-hull` starts in
the exact left-regular congruence endpoint, flips the Weyl reflection on the
rank-one vector fixed by the dihedral subgroup `<r,x>`, and obtains an exact
involution/inversion tuple with cubic energy `O(|G_p|^(-1))`.  The rank-one
projection is exactly the nonzero spectral projection of displacement from
the original endpoint, but every reducing BS carrier containing it has
rank at least `p`.  Its density still vanishes, so a qualitative slow-cut
surgery remains possible; comparable-rank or energy-linear invariantization
is rigorously false.

For orthogonal sums of those canonical cells, the moving factor is not
fatal qualitatively.  `weighted-coset-hulls-are-energy-sublinear` computes
each two-cubic Frobenius energy exactly as `24`, while its legal hull has
rank `p` inside a block of dimension `p(p^2-1)/2`.  Concavity yields, for
arbitrary prime mixtures and multiplicities,

```text
rank(total legal hull)/D <= C e^(2/3).
```

Thus legal block cutting costs `O(e^(1/3))` in normalized HS on this whole
family.  The remaining general issue is packed residual cancellation inside
one congruence block: without a decomposition into odd three-cycle cells,
small total cubic energy need not count the number of source flips to which
the concavity estimate would apply.

The hoped-for packed replacement estimate is false even without cubic
cancellation.  `packed-d-coset-flip-has-full-bs-hull` takes one coordinate
`D=<r,x>`-coset from every `B=<r,s>`--`D` double coset in a single regular
`PSL_2(F_p)` block.  Reflection across their union preserves involution and
inversion exactly, has displacement and normalized cubic energy `O(1/p)`,
but the selected coordinate vectors have `B`-orbit equal to the whole
regular block.  Hence the smallest legal BS hull has density one.  No bound
`density(Hull_B Q)<=C E^alpha`, for any positive `alpha`, can turn an
arbitrary coordinate high-displacement cut into an affordable reducing
cut.  The slow-cut theorem must therefore exploit additional structure of
its specifically decoded source (or repair it without invariantizing its
raw support); property-`(tau)` or parity rounding alone cannot fill this
gap.

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
