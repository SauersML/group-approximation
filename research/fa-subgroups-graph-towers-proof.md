---
rg: 2
id: fa-subgroups-graph-towers-proof
kind: route
title: Fix a vertex of each Bass-Serre tree and descend the tower
target: fa-subgroups-of-graph-towers-lie-in-base-pieces
requires: []
---

Induct on `n`. If `K_n` is a base group there is nothing to prove. Otherwise
`K_n` is an HNN extension of `K_i` or an amalgam `K_i *_C K_l`. It acts without
inversions on its Bass--Serre tree, and the vertex stabilizers are the
conjugates of the vertex groups. Property FA gives `L` a fixed vertex, so
`k^-1 L k <= K_i` (or `<= K_l`) for some `k in K_n`.

The conjugate `k^-1 L k` is isomorphic to `L`, so it has property FA, and it
lies in the shorter graph tower ending at `K_i` (or `K_l`) over the same bases.
By induction it is conjugate into some `B_i` inside that tower, hence inside
`K_n`. `∎`

Reference for property FA and fixed points: Serre, *Trees*, Chapter I,
Section 6.
