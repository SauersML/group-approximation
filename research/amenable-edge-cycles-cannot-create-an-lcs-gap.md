---
rg: 2
id: amenable-edge-cycles-cannot-create-an-lcs-gap
kind: claim
title: Amenable-edge cycles cannot create an LCS gap
artifacts:
  - research/amenable-edge-cycle-hyperlinearity-proof.md
distinct_from:
  word-level-seed-wirings-preserve-marked-matricial-approximability: that pulls approximations through a marked word map; this is a pointwise closure theorem for source-dependent Bass-Serre networks with no such map.
  conjugacy-actions-cannot-prune-the-odd-tv-spectrum: that explicitly induces finite-dimensional odd sectors for semidirect products; this covers arbitrary graph cycles and only concludes quantum-approximability.
  canonical-sign-corners-maximally-mix-the-tv-odd-spectrum: that computes the canonical trace on one finite torsor subgroup; this rules out a whole group-theoretic architecture independently of the chosen trace.
---

Let \(B\) be a finite linear constraint system, let \(\Gamma_B\) be its
solution group, and let \(J\) be the distinguished central involution. Suppose
that \(\Gamma_B\) is the fundamental group of a graph of groups
\(\mathcal G\) such that

1. every vertex group of \(\mathcal G\) is hyperlinear; and
2. every edge group of \(\mathcal G\) is amenable.

Then

\[
 B\text{ is tracially satisfiable}
 \quad\Longrightarrow\quad
 B\text{ is }\mathcal R^{\mathcal U}\text{-satisfiable}.                 \tag{1}
\]

Equivalently, an LCS whose solution group has such a Bass-Serre decomposition
cannot have a perfect commuting-operator strategy together with a constant
gap against finite-dimensional strategies.

The statement is pointwise: the graph, all vertex groups, all edge embeddings,
and all cycles may depend arbitrarily on the source instance. Thus source
dependence alone does not evade the obstruction. It includes iterated
amalgamated products and HNN cycles, and in particular every network made from
finite local group cells glued along finite, cyclic, abelian, or other amenable
interfaces.

There is a stronger exact conclusion for a finite graph of finite local
cells: its fundamental group is virtually free and residually finite. If
\(J\ne1\), a finite quotient detects \(J\), and the negative \(J\)-eigenspace
of the quotient's regular representation is a finite-dimensional exact
operator solution. Thus this common finite-cell architecture admits a
perfect finite-dimensional strategy, not merely near-perfect strategies.

The reason is structural. Fima and Freslon's graph-of-algebras permanence
theorem makes \(\Gamma_B\) hyperlinear. If \(B\) is tracially satisfiable,
then \(J\ne1\). Hyperlinearity keeps \(J\) nontrivial in matrix
approximations, and the Paddock-Slofstra solution-group criterion then gives
the right side of (1).

Consequently, a cyclic group-relation compiler can create a terminal
Hilbert-Schmidt obstruction only by leaving at least one hypothesis above.
The first genuine escape gates are:

- a vertex group that is already nonhyperlinear;
- a nonamenable interface;
- a noninjective coequalizer or quotient, rather than a graph of groups; or
- a non-group projector/corner relation, such as the missing TV dictator
  projector.

The claim does not say that hyperlinear profile or the required dimensions
stay small; amenable-edge cycles may cause arbitrarily severe quantitative
growth. It says that they cannot make the marked profile infinite below a
fixed error, which is what an exact commuting-versus-finite LCS gap requires.
It does not construct a nonhyperlinear group.
