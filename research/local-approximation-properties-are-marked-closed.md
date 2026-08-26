---
rg: 2
id: local-approximation-properties-are-marked-closed
kind: claim
title: Local approximation properties are hereditary, closed in the space of marked groups, and have finitely presented counterexamples
artifacts:
  - GroupApproximation/Covers/TableCover.lean
  - GroupApproximation/Covers/HyperlinearTableCover.lean
  - GroupApproximation/Sofic/Sofic.lean
  - GroupApproximation/Sofic/Hyperlinear.lean
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  clopen-non-mf-cylinder: that exhibits one nonempty clopen cylinder of non-MF marked groups cut out by a specific finite Horn sentence; this proves that the failure locus of every local approximation property is open and is exhausted by finitely presented groups, with no sentence and no specific property.
  finitely-presented-nonsofic-group-exists: that is the sofic instance of clause (iv), obtained by the finite-table cover; this is the property-free statement that the same cover works for every table-defined approximation property and that the underlying reason is topological closedness.
  continuum-nonisomorphic-non-mf-cylinder: that counts isomorphism types inside one cylinder; this is about the topology of the whole failure locus of an arbitrary local approximation property.
---

ESTABLISHED.

## Definition (local approximation property)

A **finite table** is a finite set `T` with a distinguished element `1` and a
partial binary operation, taken up to isomorphism.  For a finite subset `F`
of a group `G` write

```text
tab_G(F) := (F u F.F,  (x,y) |-> xy for x,y in F,  1).
```

A **model predicate** is any predicate `M(T, eps)` on finite tables `T` and
rationals `eps > 0` that is monotone in `eps` and passes to sub-tables
(`M(tab_G(F), eps)` implies `M(tab_G(F'), eps)` for `F' <= F`).  The
associated **local approximation property** is

```text
P_M(G)  :<=>  for every finite F <= G and every eps > 0,  M(tab_G(F), eps).
```

Instances: **sofic** (`M` = existence of a permutation model of the table with
Hamming defect `<= eps` and Hamming separation `>= 1 - eps`; this is exactly
`Covers.TableCover.TableModel` and `Sofic.IsSofic`), **hyperlinear**
(unitary models in normalized Hilbert--Schmidt distance, `Sofic.IsHyperlinear`),
**operator-MF** (unitary models in operator norm with fixed separation, by
the local normalization `isOperatorMF_iff_isNormApproximable_one` behind
[[mf-recognition-has-a-pi2-upper-bound]]), **LEF** (exact injective
multiplicative models in finite groups), **weakly sofic** (finite groups with
bi-invariant metrics), **linear sofic** (`GL_n` over a field with normalized
rank metric), and every "`C`-approximable" property for a class `C` of
metric groups.

## Theorem

For every model predicate `M`:

1. `P_M` is isomorphism-invariant and hereditary (passes to subgroups).
2. `P_M` is local: a group has `P_M` iff all its finitely generated subgroups
   do; in particular `P_M` is closed under directed unions.
3. In the space of `k`-generated marked groups, `P_M` is **closed**: if `G`
   fails `P_M` there is a radius `R` such that every marked group whose words
   of length `<= R` satisfy the same equalities as in `G` fails `P_M`.
4. If a finitely generated group `G = <X | N>` fails `P_M`, then some
   **finitely presented** group `G^ = <X | N_0>`, `N_0` a finite subset of
   `N`, fails `P_M`; the identity on `X` induces an epimorphism `G^ -> G`.
5. If `N` is recursively enumerable, `N_0` is computable from any finite
   obstruction `(F, eps)` (a finite subset and a tolerance whose table has no
   model) together with a derivation of the finitely many table equalities.

The sofic instance of 4 is machine-checked as
`Covers.TableCover.tableGroup_not_isSofic` and
`exists_finitelyPresented_cover_of_not_isSofic`.  The hyperlinear instance is
now independently machine-checked as
`Covers.HyperlinearTableCover.tableGroup_not_isHyperlinear` and
`exists_finitelyPresented_cover_of_not_isHyperlinear`, retaining the explicit
surjection onto the original group.  The argument below is the same proof with
the model predicate left abstract.

## Consequences used downstream

* `non-P_M` is an **open** subset of the space of marked groups, and the
  finitely presented groups failing `P_M` are dense in it: every failing
  marked group is the limit of its finite truncations `<X | N_0>`, and by 3
  all sufficiently large truncations fail.
* For the second-level Rice theorem
  ([[second-level-rice-theorem-for-local-approximation-properties]]) the
  only input about a property that must be supplied from outside is
  **one** finitely generated counterexample; clause 4 upgrades it to a
  finitely presented seed for the switch and for the Adian--Rabin
  construction.
* Applied to hyperlinearity: a finitely generated non-hyperlinear group has a
  finitely presented non-hyperlinear cover.  This implication is now checked
  in Lean by `exists_finitelyPresented_cover_of_not_isHyperlinear`; locality
  supplies the passage from an arbitrary counterexample to a finitely
  generated one.  This is the bridge between [[non-hyperlinear-group]] and its
  recognition-theoretic reformulation in
  [[approximation-property-recognition-dichotomy]].
