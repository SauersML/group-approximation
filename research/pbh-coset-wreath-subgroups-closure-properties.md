---
rg: 2
id: pbh-coset-wreath-subgroups-closure-properties
kind: claim
title: The subgroups satisfying the coset-wreath conditions (a)-(e) are closed under finite-index overgroups inside G, under passage from finite-index subgroups of G, and under preimages along homomorphisms to B_A groups
distinct_from:
  pbh-coset-wreaths-iff-identity-edge-hnns: that proves the equivalence of (a)-(e) and lists finite subgroups, centralizers, retracts, fixed subgroups and finite intersections as sufficient; this adds three closure operations on the class of such subgroups.
  free-group-coset-wreaths-satisfy-pbh: that needs a normal finite-index subgroup N with N ∩ C a retract of N; part 2 here removes the normality, so plain virtual retracts suffice.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED** by `pbh-coset-wreath-subgroups-closure-properties-proof` (lane proof,
elementary; not independently reviewed; no priority claimed).

## Notation

For `G ∈ B_A` write `CR(G)` for the set of subgroups `C ≤ G` satisfying the equivalent
conditions (a)–(e) of `pbh-coset-wreaths-iff-identity-edge-hnns`. For example:
- (b) `A ≀_{G/C} G ∈ B_A` for every `A ∈ B_A`;
- (e) `C = C_G(m)` for some `m` in some `B_A`-overgroup of `G`.

## Statement

Let `G ∈ B_A`.

1. **Finite-index overgroups inside `G`.** If `C' ∈ CR(G)` and `C' ≤ C ≤ G` with
   `[C : C'] < ∞`, then `C ∈ CR(G)`.
2. **From finite-index subgroups.** If `K ≤ G` has finite index and `C ∈ CR(K)`, then
   `C ∈ CR(G)`.
3. **Preimages.** If `φ : G → Q` is a homomorphism and `C' ∈ CR(Q)` (so `Q ∈ B_A`), then
   `φ^(-1)(C') ∈ CR(G)`. In particular every normal subgroup `N ⊴ G` with `G/N ∈ B_A` lies
   in `CR(G)`, as the preimage of `{1}`.

## Consequences

- **Virtual retracts.** A retract `C` of a finite-index subgroup `K ≤ G` lies in `CR(G)`.
  Combine case 3 of `pbh-coset-wreaths-iff-identity-edge-hnns` in `K` (which is in `B_A`)
  with part 2. This removes the normality requirement recorded in the Scope section of
  `free-group-coset-wreaths-satisfy-pbh`. See `virtual-retracts-satisfy-pbh-coset-wreath-closure`.
- **Commensurability.** If every finitely generated subgroup of `G` lies in `CR(G)`, the
  same holds for every group `G'` containing `G` with finite index. Indeed `G' ∈ B_A`, and for
  `C ≤ G'` finitely generated, `C ∩ G` is finitely generated and lies in `CR(G)`, hence in
  `CR(G')` by part 2, and then `C ∈ CR(G')` by part 1.
- **Fibre products:** `fibre-products-over-b-a-quotients-lie-in-cr`.
