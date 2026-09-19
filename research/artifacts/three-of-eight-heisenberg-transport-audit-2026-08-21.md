# Three-of-eight Heisenberg transport audit

Date: 2026-08-21.

The surviving question after the affine-flat classification was whether a
non-affine Boolean sum, beginning with three atoms in an eight-atom
Heisenberg context, could be named indirectly and shared across two charts by
ordinary group words.

For one literal transporter there is an exact answer, valid in an arbitrary
ambient group.  The Fourier coefficient of a three-atom sum at every element
of the rank-three context subgroup is a sum of three signs.  It is therefore
never zero.  The group-basis support of the projection is the entire context
subgroup.  If a group element conjugates this projection to another
three-atom sum, support comparison forces it to conjugate the two complete
context subgroups.  Fourier inversion then shows that it carries every atom
by one affine bijection of the Boolean cubes.

Thus the three-of-eight witness is transportable, but not selectively: a
literal group word can move it only by aligning all eight atoms.  This is
already the affine sheet-transport mechanism, not a way to identify a
nonlinear marginal while leaving the rest of the charts independently
oriented.  The theorem does not assume the ambient group finite or residually
finite, so passing from a finite Clifford packet to an infinite non-RF group
does not evade this support argument.

The boundary is equally exact.  A finite-support corner unitary with several
group-basis terms need not preserve group-basis support under conjugation;
matrix-like cancellations can carry equal-rank projections without
normalizing their diagonal algebras.  Hence the remaining Heisenberg escape
is not another literal word gadget.  It is precisely the additive/piecewise
group-algebra transport compiler already isolated by the signed-Hecke atlas.

The formal Cairn statement and proof are
`three-of-eight-transport-forces-chart-conjugacy` and
`three-of-eight-full-fourier-support-proof`.
