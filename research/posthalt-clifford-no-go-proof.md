---
rg: 2
id: posthalt-clifford-no-go-proof
kind: route
title: Exhibit the all-ranks hyperlinear model and the quotient-timing obstruction
target: posthalt-clifford-cannot-power-reverse-kleene
requires: []
---

Let `E_N` be nested extraspecial Pauli groups with one common central sign
`J`, and put `E_infty=union_N E_N`.  Every finitely generated subgroup lies
in a finite 2-group, so `E_infty` is locally finite and hyperlinear.  For
`g in E_m`, use its left-regular matrices in every `E_n`, `n>=m`.  These
define the canonical tracial ultraproduct embedding and have trace zero on
every nonidentity element; in particular `||lambda_n(J)-I||_2^2=2`.

Nevertheless every fixed finite-dimensional representation of `E_infty`
kills `J`: a nonzero `J=-1` sector would restrict to a spin sector of every
`E_N` and force dimension at least `2^N` for all `N`.  Hence exact
finite-dimensional invisibility at every rank does not imply ultraproduct
collapse.

For the timing obstruction, the reverse-Kleene machine halts only after a
finite van Kampen proof that its mark is trivial.  Relators emitted after
that halt form a further quotient, in which the same finite proof remains
valid.  They cannot resurrect the mark and so cannot establish the required
halting-side nontriviality.  These two arguments are independent of the
quality of the Clifford stability constants or the addressing mechanism.
