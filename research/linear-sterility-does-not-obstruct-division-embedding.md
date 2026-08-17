---
rg: 2
id: linear-sterility-does-not-obstruct-division-embedding
kind: claim
title: Total invisibility to finite-dimensional representations does not obstruct division-ring embedding
distinct_from:
  linnell-skew-field-can-be-centrally-infinite: that refutes the bridge from the compression defect to arbitrary division rings, using a group whose Linnell skew field is centrally infinite; this refutes the weaker bridge from the all-fields linear residual, using Higman's group, and says nothing about Linnell closures.
  compression-defect-dies-in-finite-dimensions: that says the defect always dies in finite dimensions; this says that dying in all finite dimensions -- even having the whole group die -- carries no information about division-ring embeddability.
artifacts:
  - research/artifacts/strong-atiyah-audit-2026-08-17.md
---

Let `H = <a,b,c,d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2>` be Higman's
group.  Then

* `H` is torsion-free and has **no nontrivial finite quotient**;
* consequently **every** finite-dimensional representation of `H` over
  **every** field is trivial, so the all-fields linear residual of `H` is all
  of `H`;
* nevertheless, for every field `k` of characteristic zero, `k[H]` **embeds
  in a division ring**.

The middle point is Mal'cev: a nontrivial image would be a finitely generated
linear group, hence residually finite, hence would produce a nontrivial finite
quotient of `H`.

## Sources, read this session

Fisher--Sanchez-Peralta, arXiv:2303.08165, Section 3 and Proposition 3.14:
Higman's group "can be realised as a square of groups with `BS(1,2)` vertex
groups, `Z` edge groups, and trivial face group", "was constructed by Higman
in [Hig51], and it was the first example of an infinite group with no
non-trivial finite quotients"; Rivas--Triestino "showed that Higman's group
acts faithfully and continuously on `R`, and therefore is left-orderable"
([RT19, Theorem A, Corollary B]), which also gives torsion-freeness; and
Proposition 3.14 shows `kH` "has the (a priori) stronger property of embedding
into a division ring, at least when `k` is a field of characteristic zero".

## What it rules out, and what it does not

**Rules out:** any route that hopes to obstruct division-ring embeddability --
and hence, in the intended application, `strong-atiyah-torsion-free` -- by
strengthening a *finite-dimensional* residual statement.  The strongest
possible such statement, that the entire group is invisible to every
finite-dimensional representation over every field, is realized by `H` and is
compatible with characteristic-zero division-ring embedding.  Any route from
this repository's linear residual to Atiyah therefore needs genuinely analytic
information about the regular representation.

**Does not rule out, and must not be read as:** Strong Atiyah for `H`.  The
division ring supplied by Proposition 3.14 is not asserted to be the
affiliated-operator division closure, and the paper does not claim it is.
