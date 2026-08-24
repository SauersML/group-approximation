---
rg: 2
id: bounded-dimension-microstates-force-lef-proof
kind: route
title: Compactness in one dimension, then the exact table classicalization, window by window
target: bounded-dimension-microstates-force-lef
requires:
  - exact-finite-dimensional-group-table-classicalizes
---

Fix a finite window `F<=G`; enlarge it so that `1 in F` and `F=F^(-1)`.  Let
`T` be its partial multiplication table, the set of triples `(x,y,xy)` with
`x,y,xy in F`.

**Step 1 (one dimension survives).**  Apply `(BDM1)`--`(BDM3)` with
`eps=eps_n -> 0`, giving `rho_n : F -> U(d_n)` with `d_n <= D`.  The `d_n`
take finitely many values, so some `d` occurs infinitely often; pass to that
subsequence and regard every `rho_n` as a point of the compact space
`U(d)^F`.

**Step 2 (compactness makes the table exact).**  Choose a convergent
subsequence `rho_n -> V in U(d)^F`.  Both displayed conditions pass to the
limit: `(BDM2)` gives `V_x V_y = V_(xy)` *exactly* for every triple of `T`,
and `(BDM3)` gives `||V_x - V_y||_2 >= c > 0`, hence `V_x != V_y`, for every
pair of distinct labels.  This is the point at which the dimension cap is
spent -- without it there is no compact space to converge in, and the
argument has no substitute.

**Step 3 (classicalize the exact table).**  The pair `(F,V)` is exactly the
input of `exact-finite-dimensional-group-table-classicalizes`: a finite
partial multiplication table with an exact, separated, finite-dimensional
unitary solution.  That claim supplies a finite set `X` and permutations
`sigma_x in Sym(X)` realizing every constraint of `T` exactly, with
`sigma_x` and `sigma_y` disagreeing at every point when `x != y`.

**Step 4 (read off LEF).**  `Sym(X)` is a finite group, `x |-> sigma_x` is
injective on `F` (permutations disagreeing everywhere are in particular
distinct), and it satisfies every multiplication constraint holding in `F`.
That is precisely local embeddability of the window `F` into a finite group.
Since `F` was an arbitrary finite subset of `G`, the group `G` is LEF.

**Step 5 (LEF implies sofic).**  A local embedding of `F` into a finite
group `Q` composed with the left-regular action `Q -> Sym(Q)` is a sofic
approximation of the window with multiplicativity defect `0` and normalized
Hamming distance exactly `1` between the images of distinct labels, which
beats every accuracy demand.  This is the standard implication (Gordon--
Vershik; Elek--Szabo; Weiss), imported here as a literature fact and not
reproved.

The route is a genuine reduction rather than a restatement: the prerequisite
quantifies over one table with an exact solution, while the target quantifies
over all windows of a group with only approximate solutions, and Steps 1, 2,
4 and 5 -- dimension pigeonhole, compactness, the LEF definition, and the
LEF-to-sofic import -- are supplied here.
