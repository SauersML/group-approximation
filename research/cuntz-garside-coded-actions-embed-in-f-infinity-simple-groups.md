---
rg: 2
id: cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups
kind: claim
title: A group acting faithfully by global bisections on the boundary of a Li-Garside category with finite unit groups, with no open set trapped beyond a loop and a minimal effective boundary groupoid, embeds in a simple group of type F_infinity; the host class is closed under finite-index overgroups
distinct_from:
  cuntz-stabilized-garside-full-groups-are-f-infinity: that is the finiteness half with trivial units; this adds finite unit groups, simplicity, the embedding and closure under finite-index overgroups, packaged as one host theorem.
  finitely-coded-cantor-actions-give-type-a-hosts: that needs a degree map with (UFP*) and assumes finite presentation; this needs neither, proves F_infinity, and yields simple hosts rather than type (A) actions.
  torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups: that is one application (free cubulations); this is the general interface that application instantiates.
---

**ESTABLISHED** through `cuntz-garside-coded-actions-host-proof` (lane proof, not
independently reviewed; X. Li, arXiv:2110.04505v2 and 2209.08087v2, read at source; no priority
claimed).
- The finite-unit extension of the Cuntz theorem is new here.
- It needs a referee pass. The trivial-unit core, `cuntz-stabilized-garside-full-groups-are-f-infinity`,
  was internally refereed with the Q1.15 chain.

## Statement

**Data.**
- `𝔠` satisfies the standing hypotheses of Li's `intro:Gars` (as in
  `cuntz-stabilized-garside-full-groups-are-f-infinity`).
- `𝔠` is right cancellative, so (F) holds.
- Every unit group `𝔠*(v,v)` is **finite**.
- `X ⊆ Ω_∞(𝔠)` is closed and invariant.
- `𝒢 = I_l ⋉ X`, `v_0` is an object, and `Y = X(v_0) ∩ X` has no isolated points.
- `G_2` is the Cuntz groupoid on `C = {x,y}^ℕ`.

**Conditions.**
- **(C1) Coding.** The data above.
- **(C2) Resynchronization.** A group `G` acts faithfully on `Y` by global compact open
  bisections of `𝒢|_Y`.
- **(C3) (Acyc).** For every object `v` and every non-unit `σ ∈ 𝔠(v,v)`, the set
  `∩_m σ^m·X(v)` has empty interior in `X`.
- **(C4) Dynamics.** `𝒢|_Y` is Hausdorff, effective and minimal.

**Theorem.** Assume (C1)–(C4), and put `S = F((𝒢 × G_2)|_{Y × C})`. Then:
1. `S` is of type `F_∞`. This needs only (C1) and (C3).
2. `S` is simple, perfect and integrally acyclic.
3. `g ↦ g × id` embeds `G` in `S`.
4. `S ≀ Q ≤ S` for every finite group `Q`. So the class of groups that embed in `S` is closed
   under finite-index overgroups, via the normal core and Krasner–Kaloujnine.

## What each condition asks of a geometric input

This is the anatomy of the cubulated case, `cubulated-groups-embed-in-f-infinity-simple-groups`.
Each condition was supplied by one feature of a CAT(0) cube complex, and by nothing else.

| Condition | Supplied, for cube complexes, by | Used for |
|---|---|---|
| (C1) disjoint mcms | median joins of geodesics from every vertex | Li's lcms in the bisection category |
| (C1) finite objects, Garside heights | the finite local state (a vertex, its adjacent walls, a label) and Niblo–Reeves heights | Witzel's criterion |
| (C1) finite units | properness and cocompactness (finite cube stabilizers) | `lem:Stab` |
| (C2) | "leaving a wall's carrier is permanent", so promises (flags) propagate like crossings | every element is a global bisection |
| (C3), (C4) | free exits: `G * F_r` with an exit edge at every vertex, and trivial exit stabilizers | no open set beyond a loop; topological freeness; minimality |

What is **not** used:
- curvature beyond these combinatorial facts;
- specialness, hyperbolicity or residual finiteness;
- Li's loop condition (`t<d`), a degree map, or a Perron condition.

## Consequences for non-cubulated inputs

- **Median joins are more than Li needs.** Li needs disjoint mcms, not joins. The median joins
  used here come from the median-graph structure of the 1-skeleton, and an infinite Kazhdan
  group has no proper action on a median graph (Niblo–Reeves; Chatterji–Druţu–Haglund). So Kazhdan inputs
  must enter through non-median codings with disjoint mcms, such as grid codings with
  `k`-graph combinatorics.
- **Ã₂ lattices.** The Robertson–Steger 2-graph codings used in
  `a2-lattices-satisfy-permutational-boone-higman` are the natural candidates for (C1) and (C2).
  With them the theorem would need no loops or powers, only (C3) and (C4). None of this is
  checked here.
- **C̃_n lattices.** The locally forced seeds of `cn-building-lattices-carry-locally-forced-seeds`
  (`21cd0dd3e`) are candidate states. The test is exactly (C1)–(C4):
  - (C1): do seed-labelled geodesics form a category with disjoint mcms and a left-divisor-closed
    height?
  - (C2): is there a promise move for the passive link factor, playing the role of the flag?
  - (C3), (C4): these come from exits, provided the coding of a tree of buildings is the free
    product of codings. That is expected but not proved in general.

## Lesson for general BH

For simple `F_∞` hosts, a geometric group has to supply exactly **a finite-state coding of
its boundary whose prefix order has disjoint mcms, together with promise moves that make
codings from different base points resynchronize.** The rest is free:
- the Cuntz factor supplies merge packing, and with it finiteness;
- free exits supply topological freeness, (Acyc) and minimality;
- Li's Corollary D and Matui supply simplicity.

So the question "does class `𝒞` satisfy Boone–Higman?" becomes, for geometric classes, "do its
spaces have a finite-state, promise-closed prefix order with disjoint mcms?" Median geometry is
one sufficient answer. It is not the only one, and it is the one that excludes Kazhdan groups.
