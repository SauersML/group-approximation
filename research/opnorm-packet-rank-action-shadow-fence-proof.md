---
rg: 2
id: opnorm-packet-rank-action-shadow-fence-proof
kind: route
title: Combine exact packet rounding with the finite-actor and opposite-root boundary
target: opnorm-packet-rank-does-not-yield-action-shadow
requires:
  - opnorm-packet-exactification-is-dimension-free
  - finite-group-opnorm-support-profile
  - binary-leavitt-finite-actor-minimal-atom-dichotomy
---

Operator-norm packet exactification supplies exact matrix units and, when two
approximate packet identities are close, one common identity projection.  Its
proof uses the `<1` projection threshold only after the two projections have
already been shown close.  The finite-group support-profile theorem likewise
records the ranks of central isotypic projections after a fixed finite group
table has been exactified.  Neither theorem creates closeness, commutation, or
a common refinement between projections belonging to distinct packet
algebras.

Apply the finite-actor/minimal-atom dichotomy.  If all selected transports
normalize one finite root window, `(FAM1)` is an exact finite matrix model of
all available inputs, including a surviving marked atom and arbitrary
multiplicity gauges, but its atom returns are rank-neutral and cannot satisfy
the Leavitt dimension equation.  Thus no argument using only those exactified
ranks and covariance data can produce the desired return.

If a genuine opposite-root word is included, `(FAM4)--(FAM5)` shows by direct
two-by-two multiplication that it does not normalize the root packet.  It
therefore does not define a map of its character atoms, so there is no finite
action table on which packet exactification or rank rigidity can operate.
Putting another exact packet on the same identity carrier changes none of
this: a common identity is not a common diagonal algebra.

These exhaustive cases prove the stated fence.  They do not refute a future
coefficient-sensitive moving-occurrence compiler, and they do not assume that
the ambient Leavitt group is MF.  They show only that the currently available
fixed-packet exactification and `<1` rank facts do not supply the missing
shadow-to-action converter.
