---
rg: 2
id: free-product-with-f2-upgrade-proof
kind: route
title: Paschke-Salinas for the C*-side, Bass-Serre for property (T), subgroup closure for the rest
target: free-product-with-f2-upgrade
requires: []
---

## Why sufficient

**C*-simplicity and unique trace.**  Paschke--Salinas, *C\*-algebras associated
with free products of groups*, Pacific J. Math. 82 (1979), 211--221: if
`G = A * B` with `|A| >= 2` and `|B| >= 3`, then `C*_r(G)` is simple with a
unique tracial state.  Here `|H| >= 2` since `H` is nontrivial, and `|F_2|` is
infinite.  Trivial amenable radical then follows from the
Breuillard--Kalantar--Kennedy--Ozawa equivalence between the unique trace
property and triviality of the amenable radical.

**Failure of property (T).**  A nontrivial free product acts on its Bass--Serre
tree with no global fixed point: the vertex stabilizers are the conjugates of
the two factors, and no vertex is fixed by all of `G`.  By Watatani's theorem
property (T) implies property FA, so `G` does not have property (T).

**Subgroup-closed failures pass upward.**  Soficity, hyperlinearity, the MF
property, LEF, LEA, amenability, linearity, the Haagerup property, orderability
and torsion-freeness are all inherited by subgroups.  If `P` is such a property
and `H` fails `P`, then `G` fails `P` too, since `H <= G` and `P` holding for
`G` would force it for `H`.  This is the only step used, and it is why the
upgrade costs nothing.

**Finiteness and decidability.**  A free product of finitely generated groups is
finitely generated on the union of generating sets; a free product of finitely
presented groups is finitely presented on the union of presentations with no
new relators.  The normal form theorem for free products reduces the word
problem of `G` to those of `H` and `F_2`, so `G` has solvable word problem when
`H` does.  The same normal form reduces conjugacy in `G` to conjugacy in the
factors, so `G` has solvable conjugacy problem when `H` does.

## What this does not give

Nothing about `H`'s own approximation properties is changed or learned.  In
particular the construction cannot be iterated into progress on soficity: the
output is non-sofic exactly when the input was.
