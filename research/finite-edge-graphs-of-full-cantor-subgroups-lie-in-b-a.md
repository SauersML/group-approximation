---
rg: 2
id: finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a
kind: claim
title: A finite graph of groups with finite edge groups lies in B_A when its vertex groups sit in one full clopen-transitive Cantor group of B_A with matching edge strata, so every finite-edge graph of subgroups of Thompson's T does
distinct_from:
  free-permutational-products-preserve-pbh: that reduces amalgams and HNN extensions over finite subgroups to a conjugating overgroup (its Parts 4 and 5); this supplies that overgroup from a full Cantor host, for whole graphs of groups at once.
  faithful-finite-index-graphs-of-groups-have-type-a-overgroups: that treats graphs of groups with finite-index edge groups acting faithfully on the tree; this treats finite edge groups, with vertex groups that may have no finite quotients.
  pbh-class-closed-under-common-retract-amalgams: that needs edge groups that are retracts of both sides; the finite edge groups here are retracts of neither side in the examples (T is simple).
artifacts:
  - research/artifacts/gq-bh-bh-free-10-free-permutational-products.md
---

**ESTABLISHED** by `finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a-proof` (lane
proof, not reviewed; no priority claimed).

## Statement

Let `D ≤ Homeo(Y)` be full and clopen transitive with `D ∈ B_A`, as in
`finite-subgroups-of-full-cantor-groups-conjugacy-criterion`. By
`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`, `D ∈ B_A` holds whenever `D`
is finitely presented.

Let `𝒢` be a finite connected graph of groups with:
- vertex groups `G_v`;
- finite edge groups `C_e`, with monomorphisms `α_e: C_e -> G_(o(e))` and
  `ω_e: C_e -> G_(t(e))`;
- embeddings `ι_v: G_v -> D`.

Suppose that for each edge `e`, the finite subgroups `ι_(o(e)) α_e(C_e)` and
`ι_(t(e)) ω_e(C_e)` of `D` have clopen fixed sets. Suppose also that their type sets
correspond under `ω_e α_e^(-1)`, for instance because both act freely on `Y`. Then
`π_1(𝒢) ∈ B_A`. So `π_1(𝒢)` embeds in a finitely presented simple group, and it has
solvable word problem when it is finitely generated.

**Padded form.** It is enough that the *padded* type sets `Σ^+ = Σ ∪ {whole group}`
correspond. Compose every `ι_v` with the padding `π_U` of
`finite-subgroups-of-full-cantor-groups-conjugacy-criterion`, Part 4. This adds the
whole-group stratum to every edge group at once. In particular it suffices that every
point stabilizer of every edge group, under both embeddings, is trivial or the whole edge
group. That holds for edge groups of prime order.

## Examples

- **Thompson's `T`.** Every finite subgroup of `T ≤ V` acts freely on the Cantor set. So
  **every finite graph of groups whose vertex groups are subgroups of `T` and whose edge
  groups are finite lies in `B_A`**, whatever the edge maps are. For instance, with `r ∈ T`
  of order 3:
  - `⟨T, t | t r t^(-1) = r^2⟩`, although `r` and `r^2` are not conjugate in `T`;
  - the twisted double `T *_(Z/3) T`, along `r -> r` and `r -> r^2`.

  These groups are finitely presented. They are not residually finite, since `T` is
  infinite and simple. So finite-quotient arguments do not reach them, and neither does
  the retract closure.
- **Subgroups of `V`.** The same holds for any finite graph of subgroups of `V` whose edge
  groups have matching padded type sets. For example:
  - edge groups of prime order, with arbitrary edge maps;
  - `⟨V, t | t c_1 t^(-1) = c_2⟩` for a free involution `c_1` and an involution `c_2`
    with a fixed cone. Their padded type sets are both `{1, Z/2}`.

## Scope

- **Intermediate strata.** Padding only adds the whole-group stratum. Edge groups whose
  intermediate strata differ under the two embeddings are not covered. An example is a
  Klein four-group of `V` acting freely, versus one with a cone stabilized exactly by one
  involution. This is the test case of `pbh-closed-under-finite-edge-graphs-of-groups`.
- **One host.** All vertex groups must embed in the same full host `D`.

## Lesson for general BH

For combination theorems in `B_A`, the actor is never the problem. Once the vertex groups
sit in one full Cantor host, every finite edge whose local strata match is realized by
gluing, and centralizing HNN extensions over finite subgroups finish the job. The only
obstruction left is the type set of edge groups. Finite-edge closure of `B_A` therefore
reduces to a *stabilization* problem: embed a group of `B_A` in a full host in which
prescribed finite subgroups have prescribed strata, for example act freely.
