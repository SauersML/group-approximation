# Fano one-ghost compiler audit (2026-08-22)

## Established from the supplied argument

- For `R_*=\{x:sum x_i=1\}\setminus\{1000\}`, explicit closure failures
  verify every Schaefer tractable class is absent.  Thus `CSP(\{R_*\})` is
  NP-complete.
- Translation by the ghost gives the seven nonzero points of `F_2^3`.
  A support's affine hull reintroduces the ghost exactly when the translated
  support contains a Fano line.  This is recorded with proof in
  `rstar-fano-ghost-affine-hull-criterion`.
- The pairwise pruning rule is valid.  The stronger commuting-neighborhood
  inequality is also valid without assuming the distinguished atom commutes
  with the neighbors; only the neighbor PVM algebras must mutually commute.
- If one tracial support profile consists of Fano caps, its affine-support
  LCS remains inside the original predicate.  Therefore non-RU soundness is
  preserved.  This is a complete conditional theorem, not yet a uniform
  compiler.
- For an identity-word diagram using relator type `r` with multiplicity
  `m_r`, weighted Cauchy--Schwarz gives the claimed energy bound
  `4/(sum_r m_r^2/p_r)` at mark distance two.  The optimized distribution is
  `p_r proportional to m_r`, so weighting cannot beat inverse square area for
  one fixed diagram.

## Standard affine-source no-gos retained

- The graph-colouring edge relation has a universal odd-subset ghost for
  every `k>=3`: on every edge use the allowed pairs
  `(1,2),(2,3),(3,1)`. Both endpoint parity marginals agree, so these choices
  glue on every graph independently of colourability. For `k=3`, direct
  enumeration gives all sixteen pairs in `{100,010,001,111}^2`, with two
  odd-subset witnesses per pair.
- Positive one-in-three has affine hull `x+y+z=1`; its sole added point is
  `111`, and the global all-ones assignment realizes that ghost in every
  clause. Standard `3-OR` and `NAE-3` have full affine hull, while
  exact-two-of-three has the even-parity plane.

These exact finite calculations are fenced source-selection failures, not a
general odd-subset compiler theorem. Cairn's broader
`linear-encoding-lcs-admits-odd-subset-cheats` claim remains open because
cross-context encodings require a local extendability hypothesis.

## Items not promoted to established claims

- The counts “all 12 arity-three derived hyperplanes are bijunctive” and
  “all 56 arity-four derived hyperplanes are NP-hard” depend on an unstated
  derivation/restriction convention and were supplied only as finite
  enumeration outcomes.  They need a certificate table listing each derived
  relation and an explicit polymorphism closure witness before entering the
  dependency graph.  Neither count is needed for the Fano criterion.
- The cited Taller--Vidick result is consistent with Cairn's existing audit:
  its fixed-support/decoder statements use a noise parameter
  `epsilon in (0,1)` and do not establish the perfect-completeness endpoint
  `epsilon=0`.  It therefore does not close the cap-profile selector.
- Model-by-model pruning to some Fano cap is not a uniform finite compiler.
  Different strategies may leave different caps.  A finite OR over cap
  profiles is not automatically a solution group with one central mark;
  identifying branch signs implements an AND.  This is isolated as
  `culf-mastel-rstar-uniform-fano-cap-profile`.

## Kleene orientation

The orientation itself is valid.  The established Culf--Mastel node records

```text
HALT     -> perfect CE model,
NONHALT  -> constant CE gap.
```

This is exactly the RE orientation consumed by
`re-oriented-lcs-compiler-gives-nonhyperlinear-group`.  The conditional
Theorem 8.1-style conclusion is valid only after an effective uniform
predicate-to-mark compiler supplies one finite LCS/group on both branches.
The Fano argument proves local soundness for a fixed cap profile, but not
that uniform selection step.  Reversing the Kleene branches is neither
necessary nor justified by the cited family.

## Source boundary -- corrected fixed-language audit

The fixed-language step itself is already published.  Culf--Mastel Theorem
4.14 applies to every NP-complete Boolean language, and `R_*` is additionally
non-TVF because every two-coordinate projection is full.  Corollaries 4.17
and 4.18 therefore give a total finite `R_*` family with a constant gap in
the assignment-with-commutation model.  Proposition 6.2 supplies the robust
one-constraint commutativity gadget.  What remains inside the selector node
is not language reduction but the stronger Fano interface: their commutator
weight covers variables sharing one context, not mutually different
neighbors around a context, and no uniform cap profile is selected.
