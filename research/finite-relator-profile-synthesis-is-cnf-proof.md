---
rg: 2
id: finite-relator-profile-synthesis-is-cnf-proof
kind: route
title: Hitting and forbidden-support conditions translate clause by clause
target: finite-relator-profile-synthesis-is-cnf
requires: []
---

For a bad cell `p`, the statement that the selected set contains at least one
relator whose violation set covers `p` is exactly the positive clause
`OR_(r:p in V_r) x_r`. Requiring this for every `p` gives the first CNF block.

For a collapse certificate `C_j`, the condition `C_j` is not a subset of the
selected set is equivalent to saying at least one member of `C_j` is not
selected, which is exactly `OR_(r in C_j) not x_r`. Conjoining these clauses
for all certificates gives the second block. The translation is reversible
clause by clause.
