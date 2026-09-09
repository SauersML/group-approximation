---
rg: 2
id: mf-radical-words-have-linear-certificates
kind: claim
title: Each MF-radical word has a finite global linear operator-norm certificate
distinct_from:
  full-mf-radical-linear-relator-inequality: That controls all generators when the whole group has full MF radical; this applies to an individual word in a proper radical and needs no perfectness hypothesis.
  sofic-radical-linear-action-criterion: That uses Hamming distance and Cartesian powers of actions; this uses operator norm and tensor powers of unitary matrices.
  hyperlinear-radical-is-finitely-witnessed: That concerns the hyperlinear radical and finite-prefix witnesses; this proves a linear operator-norm inequality for the MF radical.
artifacts:
  - research/artifacts/mf-word-linear-certificates.md
  - non_mf_groups_exist.tex
---

For `G=F_m/N` with `m` finite and any word `w in F_m`, the following are
equivalent: every homomorphism from `G` to an MF group kills `w`; some
finite `R subset N` and `eta>0` force `||w(U)-I||<1` whenever
`max_(r in R)||r(U)-I||<eta`; and some finite `R subset N` and `C>0`
satisfy

\[
 \|w(U)-I\|\le C\max_{r\in R}\|r(U)-I\|
\]

for every tuple of unitary matrices in every positive dimension. A
threshold with parameters `(R,eta)` gives the same `R` and `C=6/eta`.
Finite sets of radical words admit a common window and constant. For a
specified finite presentation, a constant exists using its listed relators
themselves, by finite normal-closure expressions.

**The estimate does not upgrade to a vector inequality (2026-09-08).**  It
bounds `w` by the largest relator error on the whole space, and that is
essential: `linear-norm-certificate-has-no-vector-form` shows that for every
nontrivial presented group, every word with nonidentity image, and **every**
finite `S` inside the normal subgroup, there are a finite unitary tuple and a
unit vector with `(s(U)-I)xi = 0` for all `s in S` and
`||(w(U)-I)xi|| = sqrt 2`.  So squaring the certificate into a
positive-operator inequality is false.  The same witness shows a common fixed
vector cannot be compressed into a finite-dimensional model of the quotient,
because the compressions are not unitary.

The proof is written mathematics; no new Lean verification is asserted.
