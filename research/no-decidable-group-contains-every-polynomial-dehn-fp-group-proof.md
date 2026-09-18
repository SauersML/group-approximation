---
rg: 2
id: no-decidable-group-contains-every-polynomial-dehn-fp-group-proof
kind: route
title: A decidable host of the BORS halting family would decide halting
target: no-decidable-group-contains-every-polynomial-dehn-fp-group
requires: [uniform-hosts-force-uniform-word-problem, polynomial-dehn-fp-groups-have-nonuniform-word-problem]
---

Let `P_e`, `H_e`, `x_e`, `y_e` be the computable family of
`polynomial-dehn-fp-groups-have-nonuniform-word-problem`, and put
`w_e := [x_e, y_e]`.

**Membership.**  Every `H_e` lies in class (1) by item (1) of that claim, and
in class (2) by item (2).  Class (2) is contained in class (3) with `C = 1`.

**Contradiction.**  Suppose `U` has solvable word problem and contains a copy
of every group in class (1), or in class (2), or in class (3).  In each case
`U` contains a copy of every `H_e`.  Clause (H) of
`uniform-hosts-force-uniform-word-problem`, applied to `(P_e, w_e)`, makes
`Z = {e : [x_e, y_e] = 1 in H_e}` decidable.  By item (4), `Z` is the set of
`e` with `phi_e(0)` halting, which is undecidable.

**Which `H_e` is missed.**  Clause (H) needs the embedding only for
`e notin Z`: its semi-algorithm for the complement uses an embedding of
`Gamma_e` only when `w_e != 1`.  So the argument shows more.  No decidable `U`
contains every `H_e` with `phi_e(0)` divergent.  For such `e` the subgroup
`<x_e, y_e>` is `F_2` with bounded distortion, by the conditional clause of
`bors-embedding-is-effective-in-the-machine`.

For class (3) the exponent `37` can be replaced by anything above `36`.  For
class (1) the exponent `18` is `2 + 4 * 4`: quadratic acceptors in BORS.  A
linear-time acceptor for `M_e` would give `n^10`, and Chornomaz--Wagner
(`quantitative-higman-embedding-with-dehn-control`) would lower the exponent
further, provided their construction is also read as uniform.  That is not
claimed here.
