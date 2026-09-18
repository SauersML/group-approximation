---
rg: 2
id: ck-finite-bi-index-hole-is-kazhdan-boone-higman-proof
kind: route
title: Pass to a maximal quotient, which the lemma makes finitely presented, or take the Kazhdan simple host as its own envelope
target: ck-finite-bi-index-hole-is-kazhdan-boone-higman
requires: [bi-index-core-makes-normals-core-class-unions]
artifacts:
  - research/artifacts/finite-bi-index-normal-lattice-collapse-2026-09-17.md
---

Throughout, `G` is finitely generated with solvable word problem. We may
assume `G != 1`: replace `G` by `G × Z/2`, which also has solvable word
problem and contains `G`.

**Clause 1.** H-fixed is the special case of H-free in which `S` is
prescribed, so it implies H-free. Suppose H-free gives
`G <= S <= Gamma` with `S` simple, `Gamma` finitely presented and Kazhdan,
`Gamma = <<g>>_Gamma`, `1 != g in G <= S`, and `r = |S\Gamma/S| < infinity`.
The hypotheses of `bi-index-core-makes-normals-core-class-unions`
hold with `s = g`. Its clause 6 gives a maximal proper normal subgroup `M`
with `T = Gamma/M` simple and finitely presented. Its clause 5 gives
property (T) for `T` and an embedding `S -> T`, hence `G -> T`. So `G`
embeds in a finitely presented simple Kazhdan group.

**Clause 2.** Let `T` be a finitely presented simple Kazhdan group
containing `G`. Pick `1 != g in G`. Put `Gamma = T` and `S = T`. Then `S`
is simple and contains `G`, `Gamma` is finitely presented and Kazhdan, and
`Gamma = <<g>>_Gamma` because `T` is simple. Also
`|S \ Gamma / S| = 1`. This is H-free for `G`.

**Clause 3.** The same two arguments with property (T) deleted everywhere.
Clause 1 used (T) only to transfer (T) to `T`.

**Clause 4.** For one envelope `(S, Gamma)` with `r < infinity`, clause 2
of the lemma makes every proper normal subgroup finitely normally
generated, in particular every maximal one, and a maximal one exists by
clause 6.

**Clause 5.** Let `M`, `T = Gamma/M` be as in clause 1, and suppose `S` is
finitely generated and its image `S_T` is a proper subgroup of `T`. Then
`T` is finitely presented, the stabilizer `S_T` of the trivial coset is
finitely generated, and there are at most `r` orbits on ordered pairs,
because the lemma's clause 5 bounds `|S_T \ T / S_T| <= r` and pair-orbits
of a transitive action are the double cosets of a point stabilizer. The
action is faithful: its kernel is a normal subgroup of the simple group `T`
contained in the proper subgroup `S_T`, so it is trivial. These are the
four clauses of a type (A) action.

∎
