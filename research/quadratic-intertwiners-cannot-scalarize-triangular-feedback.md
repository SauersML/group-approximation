---
rg: 2
id: quadratic-intertwiners-cannot-scalarize-triangular-feedback
kind: claim
title: Nonlinear quadratic intertwiners obstruct scalarization of triangular feedback
artifacts:
  - research/artifacts/gottschalk-directed-quadratic-intertwiner-rigidity-2026-09-08.md
---

On arbitrary products of directed three-cycles, every continuous
affine map intertwining Q(x)=xTx consists of oriented copies of
source triples and constant target triples 000 or 111. A bijective
affine intertwiner is therefore a coordinate permutation respecting the
directed cycles.

For continuous affine scalar G-equivariant maps intertwining Q_t with Q_s, the only
nonconstant possibilities are shifts R_h with s=hth^-1. In
particular, a scalar equivariant linear map commuting with Q_t is either zero or
a shift by an element centralizing t.

Consider the reversible two-track rule on products of genuine
three-cycles:

    F(x,y)=(x+R_h Q_t(y),y)

It has no continuous affine injective Q-encoding into an invariant
code for any target map equivariant under a transitive coordinate
action. Copies of second-track coordinates are globally fixed
on the code, while copies of first-track coordinates are not;
injectivity of the encoding forces a proper nonempty fixed-coordinate
set, contradicting transitivity. This affine corollary requires
neither target injectivity nor zero preservation, and does not
require the target action to commute with Q.

An independent obstruction allows arbitrary nonlinear encodings:
the same triangular rule
cannot be conjugated by any bijective Q-intertwiner to an
injective zero-preserving scalar binary cellular automaton.
The same obstruction applies to injective Q-intertwining encodings
into a code invariant under a transitive target coordinate action
that commutes with Q, with the target map injective,
zero-preserving, and equivariant under that action. Neither
continuity nor linearity of the encoding is needed.

For balanced triangular feedback

    F_A(x,y)=(x+A Q_t(y),y),       A1=0,

with A a continuous linear cellular automaton, AE != 0 for
E=I+R_t+R_t^2 also excludes full bijective Q-preserving conjugacies
to scalar equivariant maps. This uses a different intrinsic
stratum and does not require target zero preservation. It includes
every balanced control with nonzero (I-E)AE. Arbitrary nonlinear
invariant-code encodings for balanced controls remain unresolved here.

Thus nonlinear encodings preserving Q are excluded in these
stated scopes. Encodings that do not intertwine Q and encodings
into non-invariant codes remain outside the conclusions. No scalar
counterexample or proof of Gottschalk's conjecture is supplied.

There is a further exact limitation: if F=x+A Q on a product
of triples commutes with Q, then A=0, even without injectivity
or scalar equivariance. This does not exclude nonlinear
Q-intertwiners in general. On C_3 x C_2, rotating a triple
precisely when the other triple is 111 gives an explicit
nonlinear reversible scalar map commuting with Q.
