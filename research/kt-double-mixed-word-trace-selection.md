---
rg: 2
id: kt-double-mixed-word-trace-selection
kind: claim
title: Select canonical mixed reduced-word traces for the Kun--Thom double
distinct_from:
  kt-double-hyperlinear-iff-mixed-word-trace-selection: That established theorem identifies this condition with hyperlinearity of the fixed double; this is the still-open existence assertion for the models.
  reduced-amalgam-canonical-trace-is-mf: That asks for operator-norm MF approximation of the canonical trace and therefore implies this claim; this asks only for normalized-Hilbert--Schmidt multiplicativity and trace selection.
  kt-double-canonical-vertex-marginals-admit-large-amalgam-twists: That supplies exact canonical vertex marginals but deliberately does not control mixed reduced alternating traces; this asks for precisely that missing control.
---

**OPEN.**  For the explicit Kun--Thom pair `Gamma<G`, construct the maps
`rho_(epsilon,n)` satisfying `(KMW1)--(KMW4)` of
`kt-double-hyperlinear-iff-mixed-word-trace-selection`.

The target is genuinely mixed.  Exact finite-dimensional vertex
representations with exact agreement on `Gamma` and canonical vertex
characters already exist by
`kt-double-canonical-vertex-marginals-admit-large-amalgam-twists`, but their
two copies can be separated by a large unitary in the amalgam commutant.
Consequently no argument using only vertex exactification, vertex character
rigidity, or the two marginal traces can prove this claim.  It must make
every nontrivial reduced alternating word asymptotically traceless -- an
amalgamated-freeness or equivalent trace-selection statement.

By the equivalence theorem and the established nonsoficity of the double,
this claim is already a fixed-candidate formulation of the full separation
problem, not a reduction to a formally weaker question.

## Attempts

**Random twists of exact residual vertex models.**  The construction in
`kt-double-canonical-vertex-marginals-admit-large-amalgam-twists` conjugates
one residual vertex model by random signs in the commutant of the finite
image of `Gamma`.  This can make selected actors move by macroscopic
normalized-Hilbert--Schmidt distance and can cancel many mixed traces.
It cannot handle the decisive compressor return: in every finite-dimensional
image the closure of the infranormal subgroup is normal, so that return lies
back in the finite `Gamma`-algebra and every `Gamma`-commuting twist fixes it.
Thus exact residual models satisfy `(KMW1)--(KMW3)` but collapse the marked
mixed word instead of making it canonically traceless.

**Abstract MF symmetric amalgamation.**  Shulman's theorem supplies the
trace-blind MF ambient algebra recorded in `symmetric-double-weak-mf`, but it
does not select its reduced-amalgam trace.  Promoting that construction to
`(KMW4)` is exactly `reduced-amalgam-canonical-trace-is-mf`, a strictly
stronger open route rather than a formal consequence of MF.

The remaining models must therefore use genuinely non-exact, positive-density
normalized-HS vertex sectors while controlling mixed alternating moments.
