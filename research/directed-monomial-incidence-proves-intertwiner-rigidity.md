---
rg: 2
id: directed-monomial-incidence-proves-intertwiner-rigidity
kind: route
title: Use directed monomial incidence and intrinsic quadratic fibers
target: quadratic-intertwiners-cannot-scalarize-triangular-feedback
requires: []
artifacts:
  - research/artifacts/gottschalk-directed-quadratic-intertwiner-rigidity-2026-09-08.md
---

For a nonzero row ell of a continuous linear intertwiner, let eta
be its successor row. Intertwining gives ell(Qx)=ell(x)eta(x).
Evaluating on source unit vectors makes their supports disjoint.
An internal directed edge of supp(ell) would then occur only on
the left, so no such edge exists. Each supported coordinate has
exactly one incident monomial on the left, whereas the product
on the right joins it to every coordinate in supp(eta). Hence
eta is its single successor coordinate. Injectivity of the source
permutation forces ell itself to be a single coordinate.

This row argument only requires that the source permutation have
no cycles of length one or two. On finite target cycles, nonzero
rows propagate around the whole cycle. For affine maps, the
constant part is fixed by Q. A target triple with constant part
111 has no linear contribution, since the sole preimage of 111
under Q is 111. The other triples use the linear classification.

For the unbalanced triangular rule, an injective affine encoding
must copy every source coordinate. Its copies of second-track
coordinates are globally fixed on the encoded code; copies of
first-track coordinates are not. Constants are fixed too. This
proper nonempty fixed-coordinate set is invariant whenever the
target map is equivariant and the code is invariant under a
transitive coordinate action, a contradiction. No injectivity,
zero preservation, or continuity of the target map, or commutation
of its coordinate action with Q, is needed for this affine corollary.

For the nonlinear obstruction, source and target Q act
on products of genuine three-cycles. The all-one configuration
is the unique Q-fixed point with a singleton preimage fiber. Every
bijective Q-intertwiner preserves it. The unbalanced triangular
rule F(x,y)=(x+R_h Q_t(y),y) moves this point, whereas every
injective zero-preserving scalar binary cellular automaton fixes
both constant configurations. Hence they cannot be conjugate by
a Q-intertwiner, even a discontinuous nonlinear one.

For an injective encoding into an invariant code C, use the unique
singleton-fiber fixed point of Q restricted to C. A transitive
target coordinate action preserving C and commuting with Q fixes
that point, so it is constant. An injective zero-preserving target
map equivariant under that action fixes it, giving the same
contradiction for the unbalanced triangular rule.

Balanced feedback F_A(x,y)=(x+A Q_t(y),y), A1=0, instead fixes
the all-one point. Among Q-fixed configurations, exactly four
preimages characterizes those with one zero triple and all other
triples 111. A full Q-intertwining bijection preserves this stratum,
and scalar shifts act transitively on the target stratum. F_A fixes
every defect in the x track. If AE != 0 for E=I+R_t+R_t^2,
continuity and linearity of A supply a
triple indicator e_i with A e_i != 0, so it moves a defect in the
y track. Its proper nonempty fixed subset cannot correspond to
the fixed subset of an equivariant map on a transitive stratum.
This excludes full conjugacies without assuming target zero
preservation. The balanced invariant-code extension is unresolved:
four preimages inside C do not ensure a transitive ambient stratum.

For a separate constraint, every fiber Q^-1(q) with q a single
source unit vector has trivial translation stabilizer. If x+A Q
commutes with Q, it translates this fiber into itself by Aq,
forcing Aq=0. This for all unit vectors, together with continuity,
forces A=0. A controlled triple rotation on C_3 x C_2 supplies
a nonlinear reversible Q-intertwiner outside that feedback class.
