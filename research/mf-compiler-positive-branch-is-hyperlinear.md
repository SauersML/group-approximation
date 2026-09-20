---
rg: 2
id: mf-compiler-positive-branch-is-hyperlinear
kind: claim
title: The positive branch of the MF-safe finite-presentation compiler is hyperlinear
distinct_from:
  mf-safe-finite-presentation-compiler: that proves the positive branch is regularly operator-MF with an abstract tracial state; this asks for faithful Hilbert--Schmidt models, which need not come from the same operator-norm embedding or completion.
  sofic-safe-finite-presentation-compiler: that asks for permutation approximations; this asks for unitary Hilbert--Schmidt approximations. Approximability of a suitable regular trace is sufficient, not necessary on a fixed completion.
---

OPEN. For every finite presentation code d and every e in INF,
the finitely presented rope R_e(d) of
[[mf-compiler-is-uniform-in-finite-seeds]] is hyperlinear.

This uniform positive-branch property permits substitution of any
nonhyperlinear seed in the recognition reduction. A trivial abstract
switch value does not make the Higman output seed-independent. Below
R_e abbreviates the output for one fixed d, without identifying the
outputs for different d.

**Why it is not automatic.**  A regular operator-MF realization
`(A, rho, tr)` ([[regular-mf-central-hnn-closure]]) is an injective map
into the unitary group of an MF algebra together with *some* tracial
state restricting to the regular character.  Hyperlinearity of the group
needs finite-dimensional unitary tuples with relator defects small and
traces close to the regular character *simultaneously*. An MF-approximable
regular trace on the displayed completion would suffice, but is stronger
than the bare group target: a different unitary model could work.
Do not identify MF traces with Brown's quasidiagonal traces without the
additional completely-positive approximation hypotheses. The residually finite inputs of the compiler carry such
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
claim is the analytic member of the questions about these uniformly
constructed positive outputs.

**Historical universal shortcut, now blocked.** The branch is MF, so
[[mf-implies-hyperlinear]] implies this claim
([[compiler-branch-hyperlinear-from-mf-implies-hyperlinear]]). The
Liu--Thom/Shulman symmetric-double separation now refutes that universal
premise. This invalidates the shortcut, not this particular positive
branch and not every possible trace-compatible construction.

## Attempts

2026-09-20: retain two distinct direct attacks. First, prove the existing
dimension/defect or intrinsic HS visibility profile for the actual rope
models, not for every MF group. Second, prove
[[compiler-higman-coset-chain-is-sofic]]: the existing host-coset theorem
then constructs permutation models of every positive rope, which are
unitary models. This is a sufficient condition, not an equivalence.
Neither replacing an abstract trace by matrix traces without proof nor
testing one positive input establishes the required universal quantifier.
See `research/artifacts/liu-new-frontiers-2026-09-20.md` for the bounded
first attempts and a recognition-versus-locally-indicable-witness dichotomy.
