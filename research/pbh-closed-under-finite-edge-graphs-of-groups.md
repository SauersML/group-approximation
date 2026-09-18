---
rg: 2
id: pbh-closed-under-finite-edge-graphs-of-groups
kind: claim
title: The permutational Boone--Higman class is closed under fundamental groups of finite graphs of groups with finite edge groups
distinct_from:
  pbh-finite-edge-closure-equivalences: that proves this closure is equivalent to four other forms (finite amalgams, finite HNN, conjugacy realization, the involutive swap of A x A); this is the closure itself, open.
  finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a: that is the case where the vertex groups sit in one full Cantor host with matching edge strata; this asks for all vertex groups in B_A.
  aut-free-groups-satisfy-permutational-boone-higman: that imports closure under free products (trivial edge groups); this asks for finite edge groups.
---

**OPEN.** For every finite graph of groups with vertex groups in `B_A` and finite edge
groups, the fundamental group lies in `B_A`.

**Equivalent forms** (`pbh-finite-edge-closure-equivalences`):
- closure under amalgams over finite subgroups;
- closure under HNN extensions over finite subgroups;
- conjugacy realization: every isomorphism between finite subgroups of a group in `B_A`
  becomes inner in some overgroup in `B_A`;
- the involutive swap: `H *_(A × A) (A wr Z/2) ∈ B_A` for commuting copies `A × 1`,
  `1 × A` in `H ∈ B_A`.

**Known cases.**
- Centralized edges (`free-permutational-products-preserve-pbh`).
- Vertex groups in one full Cantor host with matching padded edge strata
  (`finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a`). Examples:
  - all finite-edge graphs of subgroups of Thompson's `T`;
  - all graphs of subgroups of `V` with edge groups of prime order.
- Vertex groups with a finite quotient injective on the edge groups
  (`pbh-finite-edge-closure-equivalences`, finite-quotient case).

**Settled test case.** `⟨V, t | t c_1 t^(-1) = c_2⟩`, for a free involution `c_1` and an
involution `c_2` with a fixed cone, lies in `B_A`. After padding, both involutions have
type set `{1, Z/2}` and are conjugate in `V`
(`finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a`, padded form).

**Test case.** In `V`, let `C_1 ≅ Z/2 × Z/2` act freely. Let `C_2 ≅ Z/2 × Z/2` have a
cone whose stabilizer is exactly one involution `⟨a⟩`. Take `θ: C_1 -> C_2` any isomorphism.
Is `V*_θ ∈ B_A`? The padded type sets are `{1, C}` and a set containing `⟨a⟩`, so padding
does not help. Diagonal embeddings into `nV` replace a type set by its closure under
intersections of conjugates (hand remark), so they do not help either. In every natural host
tried here, strata are only added, never removed.

**Route.** `finite-edge-closure-via-free-torsion-full-hosts`, through the stabilization
problem `b-a-groups-embed-in-full-hosts-with-free-torsion`.

## Lesson for general BH

The finite-edge part of any Higman-style tower for Boone--Higman is now a single local
problem: make two finite subgroups have the same strata in one full host. Nothing about
word problems or actors remains.
