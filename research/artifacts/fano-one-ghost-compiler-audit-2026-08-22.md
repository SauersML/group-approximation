# Fano one-ghost compiler audit (2026-08-22)

## Seven-character integration delta

The later full audit does not create a second compiler route.  Its genuine
delta is integrated into the existing route as follows:

- `rstar-fano-caps-have-seven-maximal-parity-covers` now records the exact
  cap census, minimum blocking sets, and the table of all seven maximal
  parity fibres;
- `rstar-cap-support-is-one-character-row` records the missing operator
  equivalence: cap support is exactly one identity `Y_a=-I` per context and
  exactly factorization through one of the `7^m` affine LCS quotients;
- `culf-mastel-rstar-halt-model-has-fano-cap-support` is now explicitly the
  **FC-char** representation theorem and remains open;
- `uniform-fano-profile-via-central-mark-or` consumes FC-char, enumerates the
  `7^m` one-row profiles, and applies the already established exact LCS OR;
- `perfect-lcs-via-rstar-fano-cap-profile` and
  `re-oriented-lcs-compiler-gives-nonhyperlinear-group` remain the canonical
  downstream conditional closure.

Thus the audit changes neither the unconditional status nor the Kleene
orientation.  It makes the open gate algebraically exact and removes the
obsolete `64^m` profile menu.

The finite checks are replayable with
`experiments/rstar_fano_geometry.py`.  Besides the cap and blocking-set
census, it confirms that the only Boolean polymorphisms of `R_*` in arities
one, two, and three are the coordinate projections.  Combined with the
standard low-arity consequence of Post's Boolean clone classification, this
is now promoted to the all-arities theorem
`rstar-polymorphism-clone-consists-only-of-projections`.  It closes uniform
coordinatewise postprocessing of finitely many models, but is not used by the
conditional Fano compiler.

## Fiberwise-selector audit

The proposed fiberwise replacement is retained in
`rstar-private-tail-fiberwise-cap-collapse`, with two corrections.

First, a common annihilator of the one or two selected tail vectors gives
`lambda dot t=0` and operator sign `+I`.  This is not FC-char: the nonzero
zero-fibre is a Fano line.  The construction still has a valid local finish,
because its new support contains at most two nonzero Fano points; a different
functional takes value one on both and gives the required `-I` character.

Second, the simultaneous replacement needs all three tail variables to be
private to each individual target occurrence.  That is not the privacy
property in Culf--Mastel Corollary 6.7.  Their auxiliary sets are private
between source contexts, while each `D_i` is an entire target CSP gadget and
may reuse auxiliaries internally.  More decisively,
`rstar-private-tail-instances-are-trivial` proves that the claimed target
syntax is always classically satisfiable, so it cannot be the published
perfect-gap family.  `culf-mastel-rstar-has-no-private-tail-form` connects
this firewall to the fixed-language gap.  FC-char therefore remains open.

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
- Model-by-model pruning to some Fano cap can be combined over the finite
  profile list by `finite-lcs-product-sign-is-exact-or`.  Its private branch
  selectors and priority corners implement OR inside ordinary LCS syntax;
  only identifying all branch signs would implement AND.
- The remaining gate is existence of at least one cap-supported perfect CE
  model on the halting branch.  Extremality and pairwise pruning do not imply
  that property, and a symmetry-equivariant maximal cap cannot be selected.

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

## Integration ledger for the supplied compiler note

| Supplied result | Cairn node | Audited status |
|---|---|---|
| positive-noise Taller--Vidick support and reweighting | `taller-vidick-positive-noise-fixed-support-reweighting` | established, with the fixed-`u` and zero-noise caveats |
| weighted proof-area estimate | same node; `weighted-relator-area-energy-bound` | established |
| colouring and positive-one-in-three ghosts | this artifact | established finite source-selection no-gos only |
| one-ghost `R_*` hardness | `rstar-fano-ghost-affine-hull-criterion`; `culf-mastel-rstar-fixed-language-gap-is-published` | established |
| seven-line Fano criterion | `rstar-fano-ghost-affine-hull-criterion` | established with the explicit incidence list |
| pairwise and joint pruning | `commuting-neighborhood-pruning-pays-atom-mass` | established; mutual neighbor commutation is load-bearing |
| cap-profile affine compiler | `rstar-fano-cap-support-preserves-nonru-affine-relaxation` | established conditional theorem |
| fixed-point conclusion | `perfect-lcs-via-rstar-fano-cap-profile`; `re-oriented-lcs-compiler-gives-nonhyperlinear-group` | valid conditional route |

The fixed-point orientation is correct, but its compiler hypothesis contains
the unresolved mathematical input.  A model-dependent support is not yet an
effective branch.  Once at least one profile is known to retain a perfect
HALT model, `finite-lcs-product-sign-is-exact-or` combines the finite profile
list exactly.

The later source audit sharpens that missing input.  By
`fano-cap-witness-sections-force-source-affine-safety`, a cap-supported lift
of an actual positive source support `S subseteq C` necessarily satisfies

```text
Aff_F2(S) subseteq C.
```

Changing pp-gadget witnesses cannot repair an affine-unsafe source support.
Culf--Mastel supply perfectness, oracularity, constant answer size, and the
fixed `R_*` gap, but not affine safety of the particular HALT support.  This
is the live gate in `culf-mastel-rstar-halt-model-has-fano-cap-support`.

An independent alternative is tracked by
`canonical-high-density-local-sector-groupifier`.  A genuinely shared
rejecting sector pays its codimension only once by
`common-meet-local-sectors-pay-one-deficit`; equal marginal Plancherel weights
do not authenticate that sharing, and literally identifying rank-one ghost
atoms classicalizes the contexts.

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
