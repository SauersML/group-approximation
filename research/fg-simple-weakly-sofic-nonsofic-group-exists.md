---
rg: 2
id: fg-simple-weakly-sofic-nonsofic-group-exists
kind: claim
title: Some finitely generated simple group is weakly sofic but not sofic
distinct_from:
  fg-simple-weakly-sofic-groups-are-sofic: that is the rigidity statement; this is its negation, recorded so that conditional refutations have a target.
  weakly-sofic-not-sofic: that separates the classes with a non-simple group, the Kun--Thom wreath; this asks for a simple separating group.
  linear-sofic-nonsofic-group: that asks for a linear sofic nonsofic group of any kind; a finitely generated simple such group, over any field, is an instance of this claim.
---

**OPEN.** There is a finitely generated simple group that is weakly sofic and not sofic. This is the
negation of `fg-simple-weakly-sofic-groups-are-sofic`.

**Sources of instances.**
- **Any linear sofic simple nonsofic group.** Linear soficity over any field implies weak soficity
  (`linear-sofic-implies-weakly-sofic-over-every-field`). So every finitely generated simple group that
  is linear sofic but not sofic is an instance.
- **The binary Leavitt unit group, conditionally.** `R^x` is finitely presented, simple and nonsofic
  (`leavitt-unit-group-is-simple-fa-nonsofic`). If the gate `binary-leavitt-unit-group-is-f2-linear-sofic`
  holds, `R^x` is an instance. Route: `rigidity-counterexample-from-leavitt-f2-linear-soficity`.
- **Finite simple targets give nothing else.** For finitely presented simple groups, weak models into
  finite simple groups exist iff the group is linear sofic over finite fields
  (`simple-group-width-over-all-finite-simple-groups`). So an instance that is not linear sofic over any
  finite field must be weakly sofic only through non-simple targets. By
  `simple-group-relator-templates-over-finite-simple-groups` and
  `relator-width-over-nilpotent-by-locally-finite-groups`, those targets are neither direct products of
  simple groups nor nilpotent-by-(bounded type).

**Calibration.** The rigidity claim implies that `R^x` is linear sofic over no field. So it implies
`non-linear-sofic-group` with the explicit witness `R^x`, and it refutes the gate
`binary-leavitt-unit-group-is-f2-linear-sofic`. Proving rigidity is at least as hard as exhibiting a
non-linear-sofic group, and the Gottschalk campaign's positive gate would refute it.

## Attempts

- **Through linear soficity of `R^x`.** Everything the gate needs is open on
  `binary-leavitt-unit-group-is-f2-linear-sofic`. `R^x` has no nontrivial finite-dimensional
  representations, so models must be genuinely almost multiplicative.
- **Through twisted non-simple targets.** Glebsky-type capped conjugation lengths on iterated wreath
  products with large tops. These are open on `simple-nonsofic-relator-width-over-iterated-wreath-products`
  (lane `ex-weak-sofic-deep-wreath`).
