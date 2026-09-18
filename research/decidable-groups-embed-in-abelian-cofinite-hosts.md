---
rg: 2
id: decidable-groups-embed-in-abelian-cofinite-hosts
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented group with a faithful, abelian-cofinite action whose point stabilizers are finitely generated (the one-dimensional Higman embedding problem)
distinct_from:
  permutational-boone-higman-conjecture: that asks for a finitely presented host whose action has finitely many orbits on pairs; this asks only for finitely generated stabilizers and one finite-rank free abelian subgroup with finitely many orbits, and its conclusion is the relative conjecture, not PBH.
  decidable-inputs-have-fp-houghton-like-shift-envelopes: that asks for finite presentation of a host containing the finitary symmetric group, which is already type (A); here the host need not contain any finitary permutation.
  cofinite-abelian-subgroups-give-relative-pbh: that is the theorem turning each such host into relative PBH; this is the open supply question for hosts.
---

**OPEN** (posed by lane bh-invent-02, 2026-09-18).

**Statement.** Let `G` be finitely generated with solvable word problem. Then `G` embeds in a
finitely presented group `D` with an action `D ↷ X` such that:
- the action is faithful;
- point stabilizers are finitely generated;
- some subgroup `A ≅ Z^n` has finitely many orbits on `X` (*abelian-cofinite*).

Call such `(D, X)` an *abelian-cofinite host*.

**Why it matters.** By `cofinite-abelian-subgroups-give-relative-pbh`, this statement implies
relative PBH for every decidable group, i.e. FFWZ's Conjecture 1.8
(`relative-permutational-boone-higman-conjecture`, route
`relative-pbh-via-abelian-cofinite-hosts`). A single input with Boone--Higman open that
embeds in such a host would already be a new case of that conjecture. The candidates are:
- `GL_n(Q)`;
- closed mapping class groups;
- `Out(F_n)`;
- Baumslag--Gersten;
- the graph Houghton groups `PB_r`.

## What is known

- **Necessary: decidability.** Every abelian-cofinite host has solvable word problem
  (`cofinite-abelian-subgroups-give-relative-pbh`, item 3). So the hypothesis on `G` cannot be
  dropped.
- **Necessary: ends.** Every orbit of a host has a Schreier graph with finitely many ends
  (same item). So the one-dimensional coordinate must be built into the host. Cocompact
  actions on locally finite trees with infinitely many ends are excluded.
- **Hosts that exist.** All of these already lie in the permutational class:
  - Houghton groups `H_n` (`n ≥ 3`);
  - `FSym(Z) ⋊ V_(2,1)(⟨a⟩)` on the integers, with the odometer as translation (lane proof), and
    `V_(2,1)(⟨a⟩)` itself (`higman-closure-of-abelian-cofinite-hosts-is-port-faithfulness`);
  - the Houghton-like groups `H_n(G)` of finitely presented strongly shift-similar `G`.

  So the statement holds for every group certified by the shift-similar route.
- **Closure** (see also `higman-closure-of-abelian-cofinite-hosts-is-port-faithfulness`: without faithfulness, hosts are closed under port amalgams, HNN extensions and free products; faithfulness is the one missing clause).
  - Finite direct products of hosts are hosts: take the product action and the product of the
    abelian subgroups.
  - Finite-index subgroups of hosts are hosts: a finite-index subgroup of `A` still has
    finitely many orbits, and the stabilizers keep finite index.
  - Finite-index overgroups are **not** settled. The induced action sees the conjugates
    `e A e^-1`, which need not be cofinite.

## How it could be attacked

1. **Higman's operations.** Is the class of groups embeddable in hosts closed under:
   - free products;
   - amalgams over finitely generated subgroups;
   - HNN extensions with finitely generated associated subgroups;
   - passing to benign subgroups?

   A Clapham-type proof, one that keeps word problems decidable, would then give the statement.
   The gluing lemma already closes the relative class under amalgams along orbit-finite
   ports. What is missing is faithfulness together with finitely generated stabilizers after
   gluing.
2. **Relaxed shift-similar envelopes.** Mallery--Zaremsky-type envelopes of `P`, with `E_2`
   replaced by the odometer group `V_(2,1)(⟨a⟩)` acting on `Z`. `E_2` contains `FSym`, which
   forces the host to be type (A) outright. The odometer group has no finitary elements, so
   only finite presentation and finitely generated stabilizers would have to be proved, and
   no finitary mixing is needed.
3. **The PBH side.** Does every type (A) actor embed in an abelian-cofinite host? If so, the
   statement sits between PBH (above) and relative PBH (below). Then Q3.4 splits into
   two steps: embedding in a host, and removing the free kernel of `Γ *_A D`.

## Lesson for general BH

Relative PBH is a Higman embedding problem with an *ends constraint*. The host must carry
three things:
- finite presentation;
- finitely generated stabilizers;
- one coarsely Euclidean coordinate (a `Z^n`-orbit structure).

It needs no high transitivity, because Houghton groups lend that through the port.
