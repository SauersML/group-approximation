---
rg: 2
id: fp-simple-nonsofic-group
kind: claim
title: A finitely presented simple nonsofic group
root: true
distinct_from:
  finitely-presented-nonsofic-group-exists: that is established and unconditional, and its witness is a finite-table Kazhdan cover which is not simple; this demands simplicity on top, and no cover construction supplies it.
  universal-leavitt-el4-nonsofic: that is a finitely generated nonsofic witness with its property profile, not known to be finitely presented; this demands a finite presentation, which is the one adjective missing from the known simple nonsofic groups.
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that establishes nonsoficity of every unit, GL and EL group of a d-ary Leavitt algebra over a finite field, all of them finitely generated; this asks for a finitely presented simple example, and supplies the input to the Boone-Higman route rather than the conclusion.
  fp-simple-full-mf-radical-group: that asks for a finitely presented simple group with full MF radical, an MF-model condition; this asks for a finitely presented simple nonsofic group, a Hamming-approximation condition. Neither implies the other, since simple-sofic-total-mf-radical is sofic with total MF radical.
  boone-higman-conjecture: that is a universal embedding conjecture about groups with solvable word problem; this is an existence statement about a single group, implied by it, so a refutation of this refutes that.
artifacts:
  - research/artifacts/boone-higman-nonsofic-envelope-2026-09-11.md
---

**ESTABLISHED (2026-09-11).** There exists a group `K` that is finitely
presented, simple, and not sofic.

Witness: the binary Leavitt unit group `L_(F_2)(1,2)^x`, through
`fp-simple-nonsofic-via-leavitt-unit-group`. Its finite presentation is Khanh,
arXiv:2609.08428v1, Theorem 6.1, read in full and verified by the literature
lane: Krstić--McCool makes `St_4` of a finitely presented ring finitely
presented, Khanh's Theorem 5.4 identifies it with `GL_4`, and leaf coordinates
give `GL_4 ≅ R^x`. With that verification the preprint caveat recorded below
is discharged. The Boone--Higman route stays as a second, independent
derivation.

## What is already known, and what exactly is missing

Each adjective pair is already realized in this graph, and only the triple is
open.

* **Finitely presented and nonsofic**, not simple:
  `finitely-presented-nonsofic-group-exists`, established and kernel-checked
  through a finite-table Kazhdan cover.
* **Simple and nonsofic**, not finitely presented: take
  `H = EL_12(L_(F_2)(1,2))`. It is simple by
  `binary-leavitt-elementary-group-is-simple` (which gives
  `EL_n(R) = GL_n(R)` simple for every `n >= 3`) and nonsofic by
  `d-ary-leavitt-groups-nonsofic-over-finite-fields` (which gives
  `EL_{m+1}` nonsofic for every `m >= 1`). It is finitely generated with
  decidable word problem and infinite, by
  `rank-twelve-leavitt-elementary-wp-decidable`.
* **Finitely presented and simple**, sofic status unknown: every Thompson-like
  group in the graph.

So the whole distance between this claim and what the repository owns is a
**finite presentation of one finitely generated simple nonsofic group**. That
is an instance of Boone--Higman, which is the content of
`fp-simple-nonsofic-from-boone-higman`.

## The full profile of a Boone--Higman envelope of H

If the conjecture holds, the envelope `K` of `H` is simultaneously

```text
finitely presented, simple, not sofic, Rad_MF(K) = K,
and with no nontrivial finite-dimensional representation
over any field.                                              (FSN1)
```

The soficity clause is this claim; the MF clause is
`fp-simple-full-mf-radical-group`. The two are independent conditions and
must not be conflated: `simple-sofic-total-mf-radical` is a sofic group with
total MF radical, so full MF radical never implies nonsoficity. They happen to
be carried by one witness because `H` satisfies both hypotheses.

## Relation to Boone--Higman

The route `fp-simple-nonsofic-from-boone-higman` proves that the conjecture
implies this claim. When it was written, the contrapositive looked usable: a
proof that every finitely presented simple group is sofic would refute
Boone--Higman.

**That attack is now closed.** The claim is true, witnessed by `R^x`, so its
negation is false and can refute nothing. What survives is the weaker
observation that Boone--Higman forces nonsoficity into the envelope of every
nonsofic admissible input, which constrains proposed universal constructions
but no longer offers a refutation.

## September 11: a literature route that may close this outright

A parallel lane reports Khanh, arXiv:2609.08428v1 (8 September 2026),
Theorem 6.1: the binary Leavitt unit group `R^x` is **finitely presented**,
with an explicit presentation in its Proposition 6.2. Combined with claims
already established here — `binary-leavitt-unit-group-is-simple` (via the
three-leaf prefix code `R^x = GL_3(R) = EL_3(R)`),
`openai-leavitt-unit-nonsofic`, and `binary-leavitt-all-ranks-full-mf-radical`
— that makes `R^x` itself a finitely presented simple nonsofic group with full
MF radical, closing this claim and `fp-simple-full-mf-radical-group` at once,
with no appeal to Boone--Higman.

That lane is landing the import as `leavitt-unit-group-finitely-presented`
plus the routes `fp-simple-nonsofic-via-leavitt-unit-group` and
`fp-simple-full-mf-radical-via-leavitt-unit-group`. The status of this root is
left to the fixpoint rather than edited here.

**The caveat is the whole of the caution.** That is a three-day-old v1
preprint whose proof has not been reviewed in this repository. Until it is,
the Boone--Higman route below remains the independently checkable one, and the
contrapositive stated above remains the usable direction. If the import
survives review, the implication does not become vacuous: it still says
Boone--Higman is at least as strong as producing such a group, and the
conjecture's negative side keeps both approximation attacks.

## Attempts

1. **Finitely present `EL_12(R)` directly.** *Superseded on 2026-09-11, if the
   import above is correct.* It was recorded as deferred with no mechanism:
   the group is defined over a Leavitt algebra with infinitely many defining
   ring relations, and no finite presentation of any `EL_n(L_(F_2)(1,2))` was
   known here. Khanh's Theorem 6.1 supplies exactly that for the unit group,
   which is `EL_3(R)`. `simple-envelope-forces-solvable-word-problem` shows any
   finitely presented simple envelope would re-prove the decidability recorded
   in `rank-twelve-leavitt-elementary-wp-decidable`, so the decidability side
   was consistent throughout and supplied no obstruction.
2. **Make the existing finite-table cover simple.** *Dies at the same place as
   every other maximal-quotient argument.* The Kazhdan cover of
   `finitely-presented-nonsofic-group-exists` is finitely presented and
   nonsofic, and a maximal proper normal quotient of it is simple; but that
   quotient is finitely presented only if the kernel is finitely normally
   generated (`fp-quotient-iff-kernel-finitely-normally-generated`), and
   `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels` shows the Kazhdan
   hypothesis does not supply that. Worse than in the MF lane: nonsoficity is
   *not* known to pass to quotients here, so even a finitely presented simple
   quotient would need its nonsoficity re-proved. `sofic-quotient-nonclosure`
   records that quotient permanence fails for soficity in general.
3. **Check whether the known finitely presented simple groups are sofic.**
   *Open in the literature, and the decisive question for this claim.* No node
   in this graph asserts soficity or nonsoficity of `V`, of `nV`, of a twisted
   Brin--Thompson group, or of a Röver--Nekrashevych group. Settling any one of
   them as sofic removes it as a candidate; settling one as nonsofic would
   establish this claim outright. This is the cheapest available attack and it
   is not blocked by anything recorded here.
