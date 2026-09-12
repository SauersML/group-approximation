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

**OPEN.** There exists a group `K` that is finitely presented, simple, and
not sofic.

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

Stated once in prose, because rg:2 records a refutation as an established
negation claim and no such claim exists:

> a proof that **every** finitely presented simple group is sofic would refute
> the Boone--Higman conjecture.

Combined with the same remark in `fp-simple-full-mf-radical-group`, this gives
two independent approximation-theoretic attacks on the negative side of a
fifty-year-old conjecture, neither of which passes through a decidability or
embedding argument.

## Attempts

1. **Finitely present `EL_12(R)` directly.** *Deferred, no mechanism.* The
   group is defined by generators and relations over a Leavitt algebra with
   infinitely many defining ring relations, and no finite presentation of any
   `EL_n(L_(F_2)(1,2))` is known here. `simple-envelope-forces-solvable-word-problem`
   shows any finitely presented simple envelope would re-prove the
   decidability recorded in `rank-twelve-leavitt-elementary-wp-decidable`, so
   the decidability side is consistent and supplies no obstruction.
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
