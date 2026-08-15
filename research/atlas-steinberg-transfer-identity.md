---
rg: 2
id: atlas-steinberg-transfer-identity
kind: claim
title: The transfer identity equates adjacent spare-index definitions under three commutations
distinct_from:
  atlas-steinberg-context-absorption: that kills ring relations in every monomial context; this equates the two nested-commutator definitions of a length-extended root element, and it is where the rank-four threshold appears a second, independent time.
  atlas-steinberg-spare-index-independence: that is the open lemma supplying this identity's commutation hypotheses at length three and beyond; this is the identity itself, unconditional given those hypotheses.
artifacts:
  - research/artifacts/atlas-completeness-derivation-2026-08-15.md
  - experiments/atlas_relator_transfer_check.py
---

**Theorem (transfer identity; Lemma 3.1 of the derivation artifact).**
Let `i, j, k, l` be four distinct indices and, in any group, let `X`
(root `(i,l)`), `Y` (root `(l,k)`), `Z` (root `(k,j)`) be given, with
`U = [X,Y]`, `V = [Y,Z]`, `T = [X,V]`.  If

```text
[X, Z] = 1,     [Y, V] = 1,     and T commutes with X, Y, V,
```

then `[U, Z] = T`, i.e. `[[X,Y],Z] = [X,[Y,Z]]`.

`[U,Z]` is the spare-`k` definition and `T` the spare-`l` definition of
the same length-extended root element, so this identity IS spare-index
independence — modulo its commutation hypotheses, which are exactly what
`atlas-steinberg-spare-index-independence` must supply at length ≥ 3.
The proof is four conjugations; it consumes four pairwise distinct
indices, making this the second independent appearance of the
[KrM, Theorem 3] rank-four threshold (the first:
`atlas-steinberg-context-absorption`).

**Machine cross-check.**  Over all 3,000 ordered index quadruples and
coefficient pairs in `Q`, both sides agree and both equal the canonical
`x_ij(ab)`; all 500 root-and-pair spare chains agree in `Q` and match
the canonical dictionary word (MSI job 15862151).  A check in `Q` cannot
prove a statement about the presented group, but a slip in the
conjugation algebra would have surfaced, and did not.
