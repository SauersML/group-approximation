---
rg: 2
id: hsiang-reduced-k0-via-universal-tester
kind: route
title: "Vanishing of K~_0 for the one universal finitely presented torsion-free group gives it for every torsion-free group"
target: hsiang-reduced-k0-of-torsion-free-group-rings-vanishes
requires: [higher-whitehead-universal-finitely-presented-torsion-free-group, torsion-free-directed-colimit-recursively-presented, reduced-k0-of-universal-fp-torsion-free-tester-vanishes]
---

Assume `K̃_0(Z[U]) = 0` for the fixed group `U`
([[reduced-k0-of-universal-fp-torsion-free-tester-vanishes]]). Let `G` be
torsion-free.

**Step 1: finitely generated recursively presented pieces.** Let `K` be a
finitely generated, recursively presented, torsion-free group. By
[[higher-whitehead-universal-finitely-presented-torsion-free-group]] there
is an embedding `K → U` inducing an injection `Wh_0(K) → Wh_0(U)`. That node
identifies `Wh_0` with the reduced projective class group:
`Wh_0(H) = π_0` of the cofibre of Waldhausen's assembly
`h(BH; K(Z)) → K(Z[H])`. On `π_0` the assembly is `Z = K_0(Z) → K_0(Z[H])`,
and `π_{−1}` of the connective homology vanishes, so
`Wh_0(H) = K̃_0(Z[H])`. Hence `K̃_0(Z[K]) → K̃_0(Z[U]) = 0` is injective, and
`K̃_0(Z[K]) = 0`.

**Step 2: colimits.** By
[[torsion-free-directed-colimit-recursively-presented]],
`G = colim_i K_i` is a directed colimit of such groups, with arbitrary
structure maps. Then `Z[G] = colim_i Z[K_i]` as rings. `K_0` commutes with
directed colimits of rings:

- a finitely generated projective module over the colimit is the image of an
  idempotent matrix `e`. Its entries come from some `Z[K_i]`, where
  `e_i^2 − e_i` maps to `0`, so it vanishes at a later stage `j`, and `e_j` is
  idempotent there;
- equality of classes in `K_0` is witnessed by finitely many matrix
  identities (stable conjugacy of block sums), which likewise hold at some
  finite stage.

So `colim_i K_0(Z[K_i]) → K_0(Z[G])` is bijective. Directed colimits of
abelian groups are exact, so the cokernels of `K_0(Z) → K_0(Z[−])` also pass
to the colimit: `K̃_0(Z[G]) = colim_i K̃_0(Z[K_i]) = 0`. QED

The converse is [[universal-tester-reduced-k0-from-hsiang]]. Together the two
routes record an equivalence, so the dependency cycle between the two claims
is intended.
