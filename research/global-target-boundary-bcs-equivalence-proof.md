---
rg: 2
id: global-target-boundary-bcs-equivalence-proof
kind: route
title: Identify compatible target signs with a fixed-rank boundary representation
target: global-chord-target-selection-is-fixed-profile-boundary-bcs
requires:
  - finite-chord-context-is-joint-table-plus-collision
  - coherent-balanced-context-permutations-would-give-a-ce-trace
---

Suppose compatible target signs have been chosen.  Literal equality on every
overlap gives one matrix `Z_x` for each shared variable.  The signs belonging
to a context commute because they are simultaneous conjugates of that
context's diagonal source signs.  The finite-family joint-table criterion
says exactly that their joint spectral projections have the ranks `N_c` in
`(GTS1)`.  This proves `(GTS2)`.

Conversely, given `(GTS2)`, use `z_(c,x)=Z_x` at every incidence.  The source
boundary signs in context `c` have joint spectral ranks `N_c(beta)` by
definition.  The target tuple has the same table by `(GTS2)`, so
`finite-chord-context-is-joint-table-plus-collision` supplies one context
unitary intertwining the entire boundary tuple at once.  Hence `(GTS2)` is
also sufficient for the fixed-target part of the construction.

If all `Z_x` commute, simultaneously diagonalize them.  Let `m_gamma` be the
dimension of the global joint eigenspace with character `gamma`.  Summing
these dimensions over extensions of `beta` gives `(GTS3)`.  Conversely an
integer solution of `(GTS3)` gives diagonal signs on a basis containing
`m_gamma` copies of `gamma`, and their context joint ranks are `(GTS1)`.

For the triangle example, a commuting pair with joint support only on `++`
and `--` has zero mismatch spectral projection, so its two involutions are
equal.  Joint support only on `+-` and `-+` similarly makes them negatives.
The three asserted identities follow and contradict `Z_1^2=1`.  This proves
that incidence balance alone does not solve even the general matrix problem.

Finally, when `B_c=U_c`, the joint spectral projections of `(Z_x)_(x in U_c)`
vanish on every forbidden assignment and sum to the identity on allowed
ones.  These are precisely the BCS context relations.  Conversely any
finite-dimensional BCS representation supplies those projections and their
integer ranks.  This proves the final equivalence and isolates private-fiber
collision as the only distinction for a proper boundary projection.

