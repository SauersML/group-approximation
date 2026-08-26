---
rg: 2
id: mf-compiler-positive-branch-is-hyperlinear
kind: claim
title: The positive branch of the MF-safe finite-presentation compiler is hyperlinear
distinct_from:
  mf-safe-finite-presentation-compiler: that proves the positive branch is regularly operator-MF, an operator-norm statement with an abstract tracial state; this asks that the regular trace be approximable by matrix traces along the MF approximation, which is what hyperlinearity of the group needs and what the compiler does not record.
  sofic-safe-finite-presentation-compiler: that asks for permutation approximations, where the Fell-absorption edge conjugacy has no reduced-normal-form counterpart; this asks only for Hilbert--Schmidt approximations, where the obstacle is narrower, namely quasidiagonality of one trace.
---

OPEN.  For `e in INF`, the finitely presented rope group `R_e` of
[[mf-safe-finite-presentation-compiler]] is hyperlinear.

**Why it is not automatic.**  A regular operator-MF realization
`(A, rho, tr)` ([[regular-mf-central-hnn-closure]]) is an injective map
into the unitary group of an MF algebra together with *some* tracial
state restricting to the regular character.  Hyperlinearity of the group
needs finite-dimensional unitary tuples with relator defects small and
traces close to the regular character *simultaneously*, i.e. that `tr` be
an MF-approximable (quasidiagonal, in Brown's sense) trace along the
approximation.  The residually finite inputs of the compiler carry such
traces (limits of normalized traces of finite quotients), and the tensor
synchronization step takes ultralimits of `tr tensor` matrix traces, so
the question is whether Shulman's central-HNN and compatible-corona
closures preserve approximability of the regular trace.

**Sufficient condition.**  It suffices that at every stage the regular
realization can be chosen with `tr` an ultralimit of normalized matrix
traces along an MF embedding of `A` into a matrix corona; then the
finite-dimensional stages give Hilbert--Schmidt approximate representations
of `R_e` whose traces converge to `delta_e`, which is a hyperlinear
approximation.

**Consequence if established.**  Through
[[hyperlinear-fp-recognition-complete-iff-nonhyperlinear-group]], the
finite-presentation row of the hyperlinear dichotomy becomes a
completeness dichotomy: a non-hyperlinear group exists iff `HYP_fp` is
`Pi^0_2`-complete.  Note that the compiler's negative branch needs only a
finitely presented non-hyperlinear seed, which
[[local-approximation-properties-are-marked-closed]] supplies from any
non-hyperlinear group.

**Companion result.**  The same positive branch is torsion-free
([[mf-compiler-positive-branch-is-torsion-free]]), which closes the
torsion-free finite-presentation cell through
[[finite-presentation-rice-criterion-via-the-fixed-positive-rope]]; this
claim is the analytic member of the same family of questions about one
explicit group.
