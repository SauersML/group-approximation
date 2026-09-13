---
rg: 2
id: self-twisted-bt-group-fp-embedding-iff-solvable-wp
kind: claim
title: A finitely generated group has solvable word problem iff its self-twisted Brin-Thompson group embeds in a finitely presented group
distinct_from:
  boone-higman-thompson-simple-envelope: that embeds a group with solvable word problem into SOME finitely generated computably presented simple group; this is about one specific simple group, G·V_G, and says it has a finitely presented host exactly when G has solvable word problem.
  clapham-fp-embedding-preserves-word-problem: that embeds G itself in a finitely presented group with solvable word problem; this is about hosts of the larger simple group G·V_G, and it is an equivalence.
  simple-envelope-forces-solvable-word-problem: that deduces a solvable word problem from a finitely presented SIMPLE envelope; this deduces it from a finitely presented host that need not be simple, using the simplicity of G·V_G itself.
artifacts:
  - research/artifacts/zp-z3-08-twisted-bt-artin-2026-09-13.md
---

**ESTABLISHED** (literature import with a written check) by
`self-twisted-bt-group-fp-embedding-iff-solvable-wp-citation`.

Let `G` be a finitely generated group, and let `G·V_G` be the twisted Brin–Thompson
group of `G` acting on itself by left translation. The following are equivalent:

1. `G·V_G` embeds in a finitely presented group;
2. `G·V_G` is computably presented;
3. `G·V_G` has solvable word problem;
4. `G` has solvable word problem.

For an Artin group `A`, `G·V_G` with `G = A` is Zaremsky's `AV_A`. So Problem 3.8 for
`A` is exactly the word problem of `A`, and
`zaremsky-3-08-twisted-brin-thompson-artin-in-fp-group` is equivalent to Charney's
Problem 10.

The proofs of all four equivalences are in the artifact §3:
- Higman's embedding theorem for (1)⇔(2);
- Kuznetsov's two enumerations for (2)⇒(3);
- the brick algorithm, with uniqueness of twists on open sets, for (4)⇒(3).
