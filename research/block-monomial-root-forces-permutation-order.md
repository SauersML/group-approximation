---
rg: 2
id: block-monomial-root-forces-permutation-order
kind: claim
title: A block-monomial root forces its permutation part to have order dividing the degree
invalidates: [kl-via-block-shift-hilbert-hotel]
distinct_from:
  block-monomial-coordinate-collapse: that is about trace-preserving models of the Kun--Thom wreath and says the permutation part of a block-monomial model is itself a sofic witness; this is an exponent-sum identity about a solution of a one-variable equation, uses no trace, no ultraproduct and no group being modelled, and its conclusion constrains the root rather than the model.
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Fix a decomposition of the ambient space into blocks indexed by a set `J`.
The block-monomial invertibles — one nonzero block per row and column —
form a group mapping homomorphically onto `Sym(J)`, by "which block goes
where".

Let the coefficients be block-diagonal, so they map to the identity, and let
a proposed root `T` be block-monomial with underlying permutation `sigma`.
For `w` of exponent sum `m` the image of `w(T)` is `sigma^m`.  Hence

    w(T) = 1     ==>     sigma^m = 1 ,

and at `m = ±1`, `sigma = 1`.

## What it kills

The Hilbert-hotel construction: take infinitely many copies of the
coefficient data and let the root shift among them, so that the equation is
absorbed by the rearrangement.  At `m = ±1` there is nothing to absorb — the
root is forced to be block-diagonal and the shift does no work at all.  At
`|m| > 1` the permutation may be a nontrivial `m`-torsion element, so the
construction is not dead there, but it is confined to torsion of order
dividing `m` and cannot use a free or bilateral shift.

Recorded as `kl-via-block-shift-hilbert-hotel`.

## Scope

The hypothesis is used exactly twice: the coefficients are block-diagonal
(otherwise they contribute their own permutations and the identity reads
differently) and `T` is block-monomial (otherwise there is no permutation
part to speak of).  A construction whose root is only *approximately*
block-monomial, or whose coefficients permute the blocks, is untouched — the
same scope boundary that `block-monomial-coordinate-collapse` records for its
own setting, and for the same reason: exact block structure is a strong
hypothesis that a serious construction will not want to keep.
