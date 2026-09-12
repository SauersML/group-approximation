---
rg: 2
id: fp-simple-full-mf-radical-group
kind: claim
title: A finitely presented simple group whose MF radical is everything
root: true
distinct_from:
  defect-saturation-full-mf-radical: that is an established theorem producing a finitely presented torsion-free Kazhdan group with full MF residual, which is not simple and has many proper normal subgroups; this demands simplicity as well, and the whole distance between them is finite normal generation of one maximal kernel.
  simple-sofic-total-mf-radical: that is an established countable simple group with total MF radical, supplying neither finite generation nor finite presentation; this demands a finite presentation, which is exactly what that construction does not give.
  rank-twelve-leavitt-simple-non-mf: that is one explicit finitely generated simple group with full MF radical, not known to be finitely presented; this asks for a finitely presented example, and Boone--Higman applied to that group is one route here.
  boone-higman-conjecture: that is a universal embedding conjecture about every finitely generated group with solvable word problem; this is an existence statement about a single group, implied by it, so a refutation of this refutes that.
artifacts:
  - research/artifacts/boone-higman-mf-radical-bridge-2026-09-11.md
---

**OPEN.** There exists a finitely presented simple group `K` with

```text
Rad_MF(K) = K,                                               (FPS1)
```

equivalently (by the second formulation in `mf-radical-functoriality`) such
that every homomorphism from `K` to an MF group is trivial.

## Why this is a root

It is the missing corner of a square this repository has already filled on
three sides. `defect-saturation-full-mf-radical` gives **finitely presented**
with full radical but not simple; `simple-sofic-total-mf-radical` gives
**simple** with total radical but not finitely presented;
`rank-twelve-leavitt-simple-non-mf` gives **finitely generated and simple**
with full radical but no finite presentation. Nothing in the graph asserts
the conjunction, and no finitely presented simple group anywhere in the
literature has been shown to have this property.

It is also a top-level question in its own right rather than a step toward
another one: it asks for a finitely presented simple group with no nontrivial
finite-dimensional unitary approximation of any kind.

## Consequences of a witness

Let `K` be a witness. Then:

* `K` is not MF. It is nontrivial, so a faithful corona representation would
  be a nontrivial homomorphism to an MF group.
* `K` has no nontrivial finite-dimensional representation over any field.
  Via the route `fp-simple-full-mf-radical-from-boone-higman` the witness
  contains `H = EL_12(R)`; a nontrivial representation of a simple group is
  injective, so it would restrict to a faithful finite-dimensional
  representation of `H`, and `rank-twelve-leavitt-simple-non-mf` records that
  `H` has none. For a witness obtained by the other route the same conclusion
  follows from full radical directly.
* `K` is not residually finite, which for a simple group only repeats that it
  is infinite.

Nothing here asserts that `K` is nonsofic. Soficity does not imply MF-ness in
this graph: `simple-sofic-total-mf-radical` is a sofic group with total MF
radical, so the approximation content of `(FPS1)` is strictly about MF
models and must not be upgraded to a soficity statement.

## Relation to Boone--Higman

`fp-simple-full-mf-radical-from-boone-higman` proves that the Boone--Higman
conjecture implies this claim. The contrapositive is the usable direction and
is stated once here, in prose, because rg:2 records a refutation as an
established negation claim and no such claim exists:

> a proof that **no** finitely presented simple group has full MF radical
> would refute the Boone--Higman conjecture.

That is a genuine negative attack on Boone--Higman expressed entirely in this
repository's own vocabulary, and it does not pass through any decidability or
embedding argument. It is recorded so that the MF-radical machinery here is
understood to bear on Boone--Higman, not merely to sit beside it.

## September 11: a literature route that may close this outright

A parallel lane reports Khanh, arXiv:2609.08428v1 (8 September 2026),
Theorem 6.1: the binary Leavitt unit group `R^x` is **finitely presented**.
With `binary-leavitt-unit-group-is-simple` (the three-leaf prefix code gives
`R^x = GL_3(R) = EL_3(R)`) and `binary-leavitt-all-ranks-full-mf-radical`,
that makes `R^x` a finitely presented simple group with full MF radical,
closing this claim with no appeal to Boone--Higman. The same witness also
closes `fp-simple-nonsofic-group`, by `openai-leavitt-unit-nonsofic`.

That lane is landing the import as `leavitt-unit-group-finitely-presented`
plus the route `fp-simple-full-mf-radical-via-leavitt-unit-group`; the status
of this root is left to the fixpoint rather than edited here.

**Caveat.** That is a three-day-old v1 preprint whose proof has not been
reviewed in this repository. Until it is, the two routes below remain the
independently checkable ones. Note also that the attempts recorded below are
not thereby refuted: they are attacks on the *same* target by routes that do
not depend on an unreviewed import, and attempt 1 in particular remains the
right question about the defect-saturation group's normal lattice whatever
happens to the preprint.

## Attempts

1. **Take a maximal proper normal quotient of the defect-saturation group.**
   *Deferred at an identified step, and carried as an open claim.* The group
   `G` of `defect-saturation-full-mf-radical` is finitely presented with full
   MF residual, and every nontrivial quotient again has full MF residual, so a
   maximal proper normal quotient is simple with full radical. It is finitely
   presented exactly when that maximal kernel is finitely normally generated,
   by `fp-quotient-iff-kernel-finitely-normally-generated`. Zorn's lemma
   supplies a maximal kernel and nothing else. This is the route
   `fp-simple-full-mf-radical-from-fng-maximal-kernel` and its open input
   `defect-saturation-has-fng-maximal-kernel`.
2. **Get the missing finiteness from property (T).** *Dies as a general
   principle* at `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels`: a
   finitely presented torsion-free word-hyperbolic Kazhdan group can have
   continuum many maximal normal subgroups none of which is finitely normally
   generated. The defect-saturation group is itself two-generated, finitely
   presented, torsion-free, Kazhdan and acylindrically hyperbolic, so that
   obstruction applies verbatim to the general principle. It leaves the
   existential over the maximal kernels of one specific group open.
3. **Finitely present the known finitely generated witness.** That is the
   Boone--Higman question for `rank-twelve-leavitt-simple-non-mf`, which is
   why the first route requires the whole conjecture. No finite presentation
   of `EL_12(L_(F_2)(1,2))` is known, and by
   `simple-envelope-forces-solvable-word-problem` any finitely presented
   simple envelope would in particular re-prove the decidability recorded in
   `rank-twelve-leavitt-elementary-wp-decidable`.
4. **Inspect the known finitely presented simple groups.** *No obstruction and
   no witness.* The Thompson-like families (`V`, `nV`, twisted Brin--Thompson
   groups, Röver--Nekrashevych groups) are the only finitely presented simple
   groups this graph carries, and no node asserts that any of them is non-MF,
   nor that any of them is MF. This is an unexamined question in the
   literature rather than a recorded obstruction, and settling it either way
   for a single one of those families would move this claim.
