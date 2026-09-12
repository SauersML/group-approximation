---
rg: 2
id: higman-nonsofic-subgroup-free-edge-group-proof
kind: route
title: Bass--Serre case analysis on both free-group splittings of Higman's group gives the edge-group filter
target: nonsofic-subgroups-of-higman-group-have-free-edge-groups
requires:
  - higman-group-splits-as-amalgams-over-free-subgroups
  - sofic-kernel-amenable-quotient-permanence
artifacts:
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

## Why sufficient

Artifact Section 1, Theorem 1.2. Let `S` act on the Bass--Serre tree of `G_1 *_(F_ac) G_2`.

* **Every element elliptic.** `S` is finitely generated, so it fixes a vertex (Serre) and lies in a
  conjugate of the sofic group `G_1` or `G_2`.
* **A hyperbolic element and a fixed end.** The Busemann kernel is locally contained in vertex
  stabilizers, hence sofic, and the quotient lies in `Z`, so `S` is sofic by
  `sofic-kernel-amenable-quotient-permanence`.
* **Otherwise.** `S` is the fundamental group of the finite graph of groups on its minimal subtree, with
  vertex groups in conjugates of `G_1, G_2` and edge groups in conjugates of `F_ac`. If every edge group were
  amenable, hence cyclic, `S` would be sofic.

The same argument runs on `G_3 *_(F_bd) G_4`.

**Literature input, not a Cairn node:** graphs of groups with sofic vertex groups and amenable edge groups
are sofic (Elek--Szabo for amalgams, Ciobanu--Holt--Rees for graphs of groups, as cited by
`amenable-envelope-magnus-piece-sofic-proof`; not re-read by this lane).

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently.
- The elliptic case is Serre's lemma.
- In the fixed-end case, the Busemann kernel consists of elliptic elements fixing rays to one end. Finitely many share a subray, so the kernel is locally in vertex stabilizers.
- Otherwise the minimal subtree of a f.g. group has finite quotient, and cyclic edge groups would make `S` sofic.
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 23.)
