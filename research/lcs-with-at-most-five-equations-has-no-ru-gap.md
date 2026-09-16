---
rg: 2
id: lcs-with-at-most-five-equations-has-no-ru-gap
kind: claim
title: A binary LCS with at most five equations has J != 1 only through a classical or pentagram solution, so every tracial/non-RU gap system has at least six equations
distinct_from:
  lcs-occurrence-two-qc-equals-q: that bounds how often each variable occurs and allows any number of equations; this bounds the number of equations and allows columns of every weight. Neither contains the other.
  one-triple-variable-lcs-has-no-perfect-model-gap: that allows one occurrence-three variable in an otherwise graph-incidence system of any size; this allows arbitrary columns but at most five rows, and also gives a weight bound on the parity certificates of systems of any size.
  lcs-tracial-ru-gap-equiv-nonhyperlinear: that is the Paddock--Slofstra import turning a tracial/non-RU gap system into a finitely presented nonhyperlinear group; this proves such a system needs at least six equations and certificates of weight at least five.
  solution-group-central-order-is-operator-solvability: that turns J != 1 into an operator solution of possibly infinite dimension; this classifies exactly when J != 1 for at most five equations and bounds the dimension by 8.
  explicit-exact-support-lcs-witness: that asks for one explicit gap system; this is a lower bound on the size of any such system and produces none.
artifacts:
  - research/artifacts/lcs-five-equations-and-minimal-nonhyperlinear-2026-09-16.md
  - experiments/lcs-five-equations-2026-09-16/verify.py
  - experiments/lcs-five-equations-2026-09-16/verify.out
  - experiments/lcs-five-equations-2026-09-16/census6.py
  - experiments/lcs-five-equations-2026-09-16/census6.out
---

ESTABLISHED (2026-09-16), by the self-contained route
`lcs-five-equations-closure-and-pentagram-proof`.

## Setting

Let `A in F_2^(m x n)` and `b in F_2^m`. Let `Gamma(A,b)` be the solution group
with central involution `J`. It has involution variables, commutation of
variables that share a row, and row products equal to `J^(b_i)`. An operator
solution of dimension `d` is a homomorphism `Gamma(A,b) -> U(d)` with
`J |-> -I`. A **parity certificate** is a vector `y` with `y^T A = 0` and
`y^T b = 1`.

## Theorem LCS5

Let `m <= 5`. The following are equivalent.

1. `J != 1` in `Gamma(A,b)`.
2. There is an operator solution of dimension 1 or 8.
3. Either `Ax = b` has a classical solution, or all of the following hold:
   - `m = 5`;
   - every column of `A` has even weight;
   - every 2-subset of the five rows is the support of some column;
   - `b_1 + ... + b_5 = 1`.

   In this second case the solution is the sign-adjusted Mermin pentagram: ten
   3-qubit Pauli operators on the edges of `K_5`.

## Theorem CERT

This holds for any `m`. Let `y` be a parity certificate with support `S`.
Suppose either `|S| <= 4`, or `|S| = 5` and some 2-subset of `S` is not of the
form `supp(column) cap S`. Then `J = 1` in `Gamma(A,b)`.

## Corollary: a floor for the LCS route to the root

Let `(A,b)` be tracially satisfiable but not `R^U`-satisfiable, which is the
object that `lcs-tracial-ru-gap-equiv-nonhyperlinear` turns into a finitely
presented nonhyperlinear group. Then:
- `(A,b)` has at least **six** equations;
- it has no classical solution;
- every parity certificate has weight at least 5;
- every weight-5 certificate realizes all ten pairs of its support by column
  restrictions.

The number of variables is unrestricted.

The same statement for games: with at most five equations, a perfect
commuting-operator strategy exists iff a perfect finite-dimensional one does.

## Why it is true (sketch)

1. **Restrict to the certificate.** The rows of the certificate give a
   subsystem mapping into `Gamma(A,b)` with `J |-> J`. Every column meets the
   support `S` in an even set.
2. **Incidence group.** The subsystem receives a homomorphism from the
   incidence group `H(S,C)` with `prod_v gamma_v |-> J`.
3. **Abelian means `J = 1`.** For `|S| <= 5`, columns of size 4 are central.
   The rule "commutes with all but one factor of a central row product implies
   commutes with the last one" makes the edges commute. This holds for `K_4`
   in 3 steps and for `K_5` minus an edge in 12 steps, and passes to subgraphs
   by killing generators. So `H(S,C)` is abelian and `J = 1`.
4. **The one exception.** If all ten pairs of a 5-set occur, the pentagram
   gives an 8-dimensional solution for every odd right-hand side.

`verify.py` checks the pentagram exactly for all 16 odd right-hand sides and
replays the closure derivations.

## Where it stops

At six equations the Mermin--Peres magic square (`K_(3,3)`) appears. So do
columns of size 4, `S \ {u,v}`, which fail to commute only with the column
`{u,v}`, a case PRSS does not cover.

The closure rule alone is also weaker than Arkhipov's theorem on six vertices.
`census6.py` finds complete closure for 28416 labelled graphs, all planar. It
finds incomplete closure for 3655 planar and all 697 nonplanar graphs; the
octahedron is one of the planar ones. Extending LCS5 to `m = 6` is the named
next step.
