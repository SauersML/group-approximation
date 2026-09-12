---
rg: 2
id: atlas-steinberg-transfer-identity
kind: claim
title: The transfer identity equates adjacent spare-index definitions under three shorter commutations
distinct_from:
  atlas-steinberg-context-absorption: that kills ring relations in every monomial context; this equates the two nested-commutator definitions of a length-extended root element, and it is where the rank-four threshold appears a second, independent time.
  atlas-steinberg-spare-index-independence: that is the joint-induction theorem this identity feeds — the identity is an ingredient of the induction, whose hypotheses it consumes one length down; the two are separate because the identity is a bare group statement while the induction is about the presented group.
artifacts:
  - research/artifacts/atlas-completeness-derivation-2026-08-15.md
  - research/artifacts/steinberg-spare-index-2026-08-15.md
  - experiments/atlas_relator_transfer_check.py
---

**Theorem (transfer identity, corrected form).**  Let `i, j, k, l` be
four distinct indices and, in any group, let `X` (root `(i,l)`), `Y`
(root `(l,k)`), `Z` (root `(k,j)`) be given; put `U = [X,Y]` (root
`(i,k)`), `V = [Y,Z]` (root `(l,j)`), `T = [X,V]` (root `(i,j)`).  If

```text
[X, Z] = 1,      [U, V] = 1,      [V, Z] = 1,
```

then `T = [U,Z]`, i.e. `[X,[Y,Z]] = [[X,Y],Z]`.

*Proof.*  Two applications of `[ab,c] = a[b,c]a^{-1}·[a,c]`.  Since
`[X,Z] = 1`,
`XVX^{-1} = [XYX^{-1}, XZX^{-1}] = [UY, Z] = U[Y,Z]U^{-1}·[U,Z]
= UVU^{-1}[U,Z]`, so `T = XVX^{-1}V^{-1} = UVU^{-1}[U,Z]V^{-1}`.  Now
`[U,V] = 1` collapses `UVU^{-1}` to `V`, and `V` commutes with `U` and
with `Z`, hence with the word `[U,Z] = UZU^{-1}Z^{-1}`; so
`T = V[U,Z]V^{-1} = [U,Z]`.  ∎

**What changed (correction 2026-08-15, night).**  The earlier statement
of this node assumed `[X,Z] = 1`, `[Y,V] = 1`, and that `T` commutes
with `X`, `Y` and `V`.  The last three are statements about the
length-`t` object at root `(i,j)` — the object the induction is
constructing — and were the entire source of the stall recorded in the
derivation artifact.  They are not needed: `T`'s own commutations are a
*consequence* (`V` commutes with `U` and `Z`, hence with `[U,Z]`), not a
hypothesis, and `[Y,V] = 1` is not needed at all.  The two hypothesis
sets are not comparable — the corrected form asks for `[U,V] = 1` and
`[V,Z] = 1`, which the old one did not — but every corrected hypothesis
is an (St2) instance between **strictly shorter** objects at roots other
than `(i,j)`:

```text
[X,Z] = 1    roots (i,l),(k,j)    index-disjoint    —   l ≠ k,  j ≠ i
[U,V] = 1    roots (i,k),(l,j)    index-disjoint    —   k ≠ l,  j ≠ i
[V,Z] = 1    roots (l,j),(k,j)    SAME-TARGET       —   j ≠ l,  j ≠ k
```

so all three are supplied by an induction hypothesis one length down,
with no spare-index clash.  The same-target instance is load-bearing: an
emitter that read the (St2) side condition as "index-disjoint roots"
would omit it and this identity would be unusable.
`experiments/atlas_relator_rank5_full_family.py:159-164` guards with the
genuine condition (`i != ell and k != j` over `combinations(roots, 2)`),
so all 120 qualifying unordered root pairs — 60 index-disjoint, 30
same-source, 30 same-target — are emitted at all 25 coefficient pairs.

**Index budget.**  The identity consumes four pairwise distinct indices,
so it remains the second independent appearance of the [KrM, Theorem 3]
rank-four threshold (the first: `atlas-steinberg-context-absorption`).
The induction that *supplies* its hypotheses is a separate matter and
needs `n ≥ 5`; this node is not a rank-four completeness statement.

**Machine cross-check.**  The conclusion was verified over all 3,000
ordered index quadruples and coefficient pairs in `Q` (MSI job
15862151); both hypothesis sets hold there, so that run is evidence for
the identity and silent on the hypothesis structure — which is exactly
where the original statement was wrong.  The corrected hypothesis set
was then checked **exhaustively** over `S₅` (all 1,728,000 ordered
triples; `experiments/atlas_relator_i2_route_check.py`, MSI job
15865413): the conclusion holds in every one of the 24,960 triples
satisfying all three hypotheses; **each hypothesis is load-bearing**
(dropping `[X,Z]`, `[U,V]`, `[V,Z]` admits 84,600 / 4,320-of-4,320 /
8,400 violations respectively); and `[Y,V] = 1` is confirmed
superfluous by 4,200 direct witnesses satisfying the three hypotheses
with `[Y,V] ≠ 1` and zero violations.  A group identity cannot be
proved by testing groups — the proof is the five lines above — but this
battery would have caught a wrongly stated hypothesis set.  The
methodological lesson is recorded in the trap ledger: `[Y,V] = 1`
happens to hold in the atlas configuration (3,000 of 3,000), so no
test in the intended model could ever have exposed it as unnecessary —
verification in the target model confirms conclusions; only abstract
testing, where hypotheses can fail independently, audits hypotheses.
