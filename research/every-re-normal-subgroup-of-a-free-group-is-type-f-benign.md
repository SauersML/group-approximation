---
rg: 2
id: every-re-normal-subgroup-of-a-free-group-is-type-f-benign
kind: claim
title: "Open: every recursively enumerable normal subgroup of a finitely generated free group is type F benign (the benign half of Higman's theorem with type F witnesses)"
root: true
distinct_from:
  two-occurrence-realizability-is-type-f-benignness: That proves the equivalences, the closure properties, the reduction to Higman's universal group and the halting-subgroup base case; this is the open universal statement those reduce the two-occurrence window to.
  every-finitely-presented-group-embeds-in-an-f-infinity-group: That is an embedding statement, impossible in type F for groups with torsion and blocked above FP_2 for the rope trick; this asks only for a type F group Λ ⊇ F and a type F subgroup Σ with Σ ∩ F = N, which every finite group already satisfies.
---

**OPEN.** For every finite `A` and every normal subgroup `N ⊴ F(A)` that is
recursively enumerable, there are a group `Λ ⊇ F(A)` of type `F` and a
subgroup `Σ ≤ Λ` of type `F` with `Σ ∩ F(A) = N`.

**Equivalent forms** (`two-occurrence-realizability-is-type-f-benignness`,
items 1 and 3).
- It is equivalent to the same statement for the single relation subgroup
  `N_U ⊴ F(B)` of Higman's universal finitely presented group `U`, which is the
  normal closure of finitely many words.
- It is equivalent to: every finitely generated recursively presented group
  `G` is a section `D/(D ∩ Σ)` of a type `F` group, with `Σ` of type `F`.
- It is equivalent to: every such `G` has a type `F` Mikhailova triple
  `(H, S, phi)` with `WP(G) = phi^{-1}(S)`.
- It is equivalent to: the torsion-free, finitely generated, recursively
  presented double `F(B) *_{N_U} F(B)` embeds in a group of type `F`
  (`type-f-benignness-is-embedding-of-the-double`). Its `F_m` version is
  implied by `E_m`, the universal form of Zaremsky 1.1. Conversely, a
  counterexample to its `F_{n+1}` version answers Zaremsky 1.1 negatively.

**Why it matters for Zaremsky 1.1.** It implies that every such `WP(G)` reduces
to the word problem of a type `F` group by the inverse-respecting
two-occurrence pattern `X -> [X, q]`. Such reductions are linear-size. This
closes the opposite-sign two-occurrence window for word-problem obstructions
at every level `F_{n+1}`. After that, only the equal-sign pattern `X Q X = Q`
and three occurrences would remain.

**Known.**
- The base case holds for halting subgroups `T_M ≤ Z * Z^2` of modular machines (item 5 of the reduction claim).
- It holds for finite `F/N` and for subgroups of quotients `Γ/M` of type `F` groups by type `F` normal subgroups.
- The classical, finitely presented / finitely generated version is Higman's lemma.

**The exact missing step** is a type `F` witness for joins or normal closures
of type `F` benign subgroups.
