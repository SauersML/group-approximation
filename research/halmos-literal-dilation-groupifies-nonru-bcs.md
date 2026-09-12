---
rg: 2
id: halmos-literal-dilation-groupifies-nonru-bcs
kind: route
title: Groupify the non-RU BCS by dilating each involution to a literal group unitary
target: non-ru-bcs-is-satisfiable-in-a-group-factor
requires:
  - mipstar-bcs-tracial-nonru-exists
---

**INVALIDATED DILATION SHORTCUT.**  Start with a tracial satisfying tuple
of involutions for the fixed non-`R^U` BCS.  Place it in a common corner
`pMp`, apply a Julia/Halmos unitary dilation to each variable, and try to
declare the dilating unitaries to be literal generators of a countable host
group.  Free Haar tags or block permutations were intended to make the host
trace canonical while compression back to `p` retained the BCS tuple.

`unitary-corner-compressions-force-reduction` shows that the construction
has no dilation part.  Since every BCS variable is already unitary, any
literal `u_i` satisfying `p u_i p=x_i` must commute with `p`.  The common
corner is therefore an invariant group-factor corner and already solves the
target before the proposed Halmos/free-tag step.  Approximately unitary
compressions have vanishing leakage by `(UCR2)`, so an ultraproduct version
does not evade the obstruction.

The endpoint remains open: it requires constructing precisely that common
reducing corner in a group factor, not producing it functorially from
individual unitary dilations.
