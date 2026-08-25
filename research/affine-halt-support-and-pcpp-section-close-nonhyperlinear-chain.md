---
rg: 2
id: affine-halt-support-and-pcpp-section-close-nonhyperlinear-chain
kind: claim
title: Affine-safe HALT supports with coherent affine PCPP proofs close the nonhyperlinear chain
distinct_from:
  culf-mastel-rstar-halt-model-has-fano-cap-support: that asks whether the published HALT construction actually has the required support property; this proves that a precise pre-PCPP support-and-proof hypothesis has no further downstream obstruction.
  contextual-fano-cap-compiler-is-equivalent-to-perfect-lcs: that starts after a cap-supported R-star compiler is supplied; this derives that compiler from affine source supports and a coherent affine perfect-proof section and then performs the fixed-point endpoint audit.
  canonical-profile-kleene-higman: that accepts a general recursively presented group-algebra compiler and finishes through effective Higman; this stays in finite LCS syntax and uses the native central involution, so no Higman embedding is needed.
---

ESTABLISHED (conditional theorem).  Consider the effective RE-oriented
verifier family used before the final Hadamard--PCPP answer reduction in the
Culf--Mastel/DFNQXY perfect-gap construction.  Assume the following one
HALT-side property.

For every halting machine, choose a perfect Connes-embeddable strategy.  For
each source question context let

```text
S subseteq C subseteq F_2^n,
A=Aff(S).
```

Here `S` is its positive joint-answer support and `C` is the accepting
relation.  Require

```text
A subseteq C,                                                (APS1)
```

and require a choice of the honest PCPP proof data which is coherent with
the answer-reduction consistency tests and whose restriction to this context
extends to an affine map

```text
Pi:A -> F_2^P                                                (APS2)
```

such that `Pi(a)` is a perfectly accepting PCPP proof for every `a in A`.
Then one can effectively construct a finite binary LCS family satisfying

```text
M halts      => its solution-group sign J_M is nontrivial,
M nonhalts   => its finite-dimensional quantum value is <1. (APS3)
```

Consequently the proof-search recursion theorem constructs an explicit
finite presentation of a nonhyperlinear group.

The word **coherent** in `(APS2)` is essential.  Pointwise choices of proofs
only on `S`, or an affine formula whose values outside `S` are not perfect
proofs, do not imply the claim.  It is enough, and slightly weaker than one
global affine proof oracle, to require the affine extension separately on
every source support while retaining all proof-coordinate identifications
tested by the published answer reduction.

## From the affine section to an affine-safe constant-answer verifier

Hadamard encoding and restriction to a PCPP random view are linear.  Hence,
for a fixed `Verify` view `r`, the map

```text
a |-> r(Hadamard(a),Pi(a))
```

is affine on `A`.  Its image is an affine set and is contained in the
accepting `Verify` relation because every `Pi(a)` is a perfect proof.  The
observed support at `r` is contained in this image, so its affine hull is
accepted.  Thus every `Verify` support is affine-safe.  All non-`Verify`
supports are affine-safe by
`dfnqxy-answer-reduction-does-not-preserve-affine-safe-support`; equivalently
their equalities and Hadamard code/subset tests are affine relations.

This proves the exact implication which generic PCPP completeness does not:

```text
(APS1)+(APS2) => every positive post-PCPP context support T obeys
                 Aff(T) subseteq its accepting relation.     (APS4)
```

`hadamard-pcpp-reflects-affine-unsafety` proves that `(APS1)` is necessary
for this route.  `dfnqxy-pcpp-contract-allows-nonlinear-proof-views` proves
that `(APS1)` alone is not sufficient; `(APS2)`, or the direct viewwise
conclusion `(APS4)`, is the first presently unproved input.

## Effective cap compilation and NONHALT soundness

For every bounded-arity accepting relation `C`, use the single truth-table
gadget `G_C` from
`boolean-relations-have-affine-complete-rstar-pp-gadgets`.  It is computed
without knowing `S`, its visible projection is exactly `C`, and `(APS4)`
gives a deterministic witness section whose every `R_*` row lies in a Fano
cap.  Witness bits are affine functions of commuting source bits, so the
HALT strategy extends inside the same Connes-embeddable tracial algebra.
Auxiliaries are private to their source context.  The equality, Hadamard,
and final two-visible commutativity rows may equivalently use the explicit
cap-safe gadgets in `dfnqxy-nonverify-rows-have-cap-safe-rstar-pp-compilers`
and `cm-empty-replacement-is-fano-cap-safe`.

This replacement is an effective finite pp reduction.  Any exact tracial
model of the target `R_*` system restricts on the visible variables to an
exact model of the source verifier, because the visible projection of each
gadget is exactly its source relation.  Therefore a perfect
matrix-ultraproduct target model on a nonhalting input would give a perfect
Connes-embeddable source model, contradicting the published Culf--Mastel
soundness.  No quantitative pp inverse is needed for the endpoint.  For a
finite game, quantum value one would itself yield such a perfect
matrix-ultraproduct model, so the target value is strictly below one.

There are seven maximal Fano caps per `R_*` context.  Enumerate their finite
product.  For each profile, replace every context by its selected affine
parity row, retaining the shared variables.  Every branch is a finite LCS;
every branch model is an `R_*` model, while the HALT cap-supported model
belongs to at least one branch.  Apply
`finite-lcs-product-sign-is-exact-or` to the finite branch menu.  Its
selector-corner decoder shows that a marked perfect tracial model of the OR
has a nonzero corner which is a perfect model of one branch.  Thus the OR
preserves both HALT completeness and NONHALT matrix-ultraproduct soundness,
and `(APS3)` follows.  In the HALT model its standard solution-group sign is
represented by `-I`, hence is algebraically nontrivial.

## Fixed point, finite presentation, and the regular-trace contradiction

Given an index `e`, compute the finite solution-group presentation
`Gamma_e` and enumerate formal consequences until a proof of `J_e=1` is
found.  Kleene's recursion theorem gives an index `e_*` running this search
on its own output.  It cannot halt: a stopping proof says `J_(e_*)=1`, while
HALT completeness in `(APS3)` gives a representation with `J_(e_*)=-I`.
It follows that `e_*` is nonhalting.  Conversely, if `J_(e_*)=1`, completeness
of finite-presentation proof enumeration would make it halt.  Therefore

```text
e_* nonhalts and J_(e_*) != 1.                            (APS5)
```

The group `Gamma_(e_*)` is already finitely presented because it is a finite
solution group; effective Higman embedding is unnecessary.

For completeness, the final obstruction can be read directly in the
canonical trace.  If `Gamma_(e_*)` were hyperlinear, canonical normalized-HS
microstates would satisfy all solution-group relators.  Since `J` is a
nonidentity involution, the regular trace has `tau(J)=0`, and therefore

```text
||1-J||_(2,tau)^2=2.                                    (APS6)
```

In the matrix ultraproduct the exact central involution represented by `J`
has a negative spectral projection of trace `1/2`.  On this nonzero corner
`J=-1`, so the solution-group relations give a perfect Connes-embeddable LCS
model.  That contradicts the NONHALT conclusion in `(APS3)`.  Equivalently,
NONHALT soundness forces every asymptotic solution-group representation to
collapse `1-J`, whereas canonical Gram convergence forces its norm to tend
to `sqrt(2)`.  This is precisely the native central-mark instance of the
reverse-Kleene regular-trace contradiction.

Hence there is no remaining conditional gap after `(APS1)--(APS2)`.  The
first exact missing theorem is source-specific: exhibit the required HALT
strategy and coherent affine perfect-proof sections (or prove the direct
viewwise condition `(APS4)`) for the actual DFNQXY/Culf--Mastel compiler.
