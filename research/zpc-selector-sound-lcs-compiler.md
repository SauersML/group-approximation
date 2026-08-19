---
rg: 2
id: zpc-selector-sound-lcs-compiler
kind: claim
title: Tailored ZPC control compiles to an LCS with perfect-completeness and perfect-strategy sound decoding
artifacts:
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
distinct_from:
  zpc-readable-control-freezing-to-lcs: freezing seeks one invariant global readable fiber before compiling; this claim permits the compiler to retain and encode the readable control, provided perfect finite-dimensional solutions decode soundly.
  finite-linear-commutation-system-to-lcs: that is an exact syntax compiler for already-unconditional relations; this claim must first eliminate controlled branching without creating spurious finite-dimensional perfect solutions.
---

There is an effective transformation taking a finite tailored game `G` to a
finite binary LCS `L(G)` with the following two properties.

1. Every perfect ZPC-IRS strategy for `G` induces a perfect commuting-operator
   strategy for `L(G)`.
2. Every perfect finite-dimensional strategy for `L(G)` decodes to a perfect
   finite-dimensional strategy for `G`.

It is enough for the transformation to work on the fixed finite game supplied
by `perfect-zpc-irs-quantum-gap-game`.

The established `controlled-linear-predication-normal-form` gives an exact
operator-level predicated normal form for each controlled branch relation. An
actual LCS compiler must additionally present enough consistency among the
gated copies and enough mutually-exclusive/exhaustive selector semantics that a
perfect finite-dimensional LCS solution cannot satisfy incompatible branches,
evade all branches, or assign unrelated operators to the gated copies.

Three established barriers now delimit the naive selector approaches.
`one-hot-selector-parity-barrier` rules out direct parity enforcement of a
three-or-more-way one-hot selector, while `affine-auxiliary-control-flow-barrier`
shows that adding arbitrarily many existential **commuting affine auxiliaries**
does not help: projections of affine solution sets stay affine, so neither
multiway one-hot control nor a path-activation bit `t=a AND b` can be encoded
that way.  The stronger `finite-group-selector-induction-barrier` shows that
putting those commuting selector involutions inside an arbitrary standalone
**finite nonabelian group gadget** still does not help.  If `J` is the central
phase and `A=<J,z_1,...,z_m>` is the abelian selector subgroup, every character
of `A` with `J=-1` occurs in the finite-dimensional induced representation
`Ind_A^F chi`.  Thus the selector sign patterns seen by `J=-1`
representations form an affine set and cannot be exactly one-hot for `m>=3`.

The last barrier is deliberately not a no-go for this claim.  It says that a
successful compiler cannot obtain soundness from a self-contained finite
selector gadget while the visible selectors remain commuting group elements.
The remaining positive possibilities are more specific:

- couple the selector sector to the payload relations so that every invalid
  selector character is incompatible with `J=-1` in the **full** compiled
  group, even though it occurs in the selector subgroup by itself;
- encode branch sectors by spectral/central-idempotent data of a noncommuting
  payload gadget rather than by a commuting family of selector group elements;
- exploit verifier-specific identities so the relevant branch relation is
  affine after eliminating redundant readable controls.

## Attempts

- **Predicated SSA form.** Use the gated involutions `G_(a,i)` and link copies
  back to each original unreadable variable with `prod_a G_(a,i)=U_i`. This
  gives exact local completeness. The failed step is a sound LCS presentation
  of the gating/partition semantics; parity equations alone admit spurious
  representations.
- **Binary decision DAG with affine path bits — ruled out.** Replacing one
  multiway selector by binary choices does not solve the problem if a deeper
  path is represented by a classical auxiliary bit: path activation requires
  `t=a AND b`, which has no existential affine encoding. A useful binary DAG
  must avoid materializing conjunctions affinely or get the needed
  nonlinearity from operator structure.
- **Standalone finite noncommutative selector — ruled out when visible
  selectors commute.**  Arbitrary finite nonabelian auxiliary structure cannot
  remove the invalid sign characters of the commuting selector subgroup;
  induction realizes them all with `J=-1`.  Any revival must use payload
  coupling so the bad induced sectors do not extend to representations of the
  full compiler.
- **Payload-coupled phase kill.**  This is the sharpest current positive
  target.  Arrange the compiled relations so every invalid selector pattern
  forces `J=1`, while a valid one-hot pattern reduces exactly to the selected
  predicated linear system.  Because `J=-1` is the distinguished LCS sector,
  this would give perfect-strategy soundness without needing one-hot to be an
  affine relation in isolation.
- **Verifier-specific specialization.** Extract the actual readable decision
  structure of the fixed TailoredMIP witness and minimize it before designing a
  general gadget. The barriers rule out broad compiler classes but do not rule
  out a source-specific identity that eliminates branch conjunctions or makes
  invalid selector sectors phase-trivial through the payload.
