---
rg: 2
id: boone-higman-via-ck-maximal-kernel
kind: route
title: Compose the two envelope theorems and finitely normally generate one maximal kernel
target: boone-higman-conjecture
requires: [boone-higman-thompson-simple-envelope, chatterji-kassabov-normal-generator-embedding, proper-normal-subgroups-miss-the-normally-generating-core, ck-envelope-has-a-finitely-normally-generated-maximal-kernel, fp-quotient-iff-kernel-finitely-normally-generated]
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Let `G` be finitely generated with solvable word problem.

By `boone-higman-thompson-simple-envelope`, applied to `G × Z` so that the
core comes out infinite, embed `G <= S` with `S` finitely generated,
computably presented, infinite and simple.  Pick `1 != s in S`.  Since `S`
is finitely generated and recursively presented,
`chatterji-kassabov-normal-generator-embedding` applies and gives a finitely
presented `Gamma >= S` with property (T) and `Gamma = <<s>>_Gamma`.

By `ck-envelope-has-a-finitely-normally-generated-maximal-kernel` choose a
maximal proper normal `M <| Gamma` that is finitely normally generated.
Maximality makes `Gamma/M` simple.  By
`proper-normal-subgroups-miss-the-normally-generating-core`, `M ∩ S = 1`, so
`S` — and therefore `G` — embeds in `Gamma/M`.  By
`fp-quotient-iff-kernel-finitely-normally-generated`,
`Gamma/M` is finitely presented.

So `G` embeds in a finitely presented simple group.

## Why every prerequisite is genuinely used

Drop the Thompson envelope and there is no simple core, so the quotient can
kill `G`.  Drop the Chatterji--Kassabov envelope and there is no finitely
presented ambient group, so there is nothing to take a quotient of.  Drop the
core-survival lemma and a maximal quotient is simple but possibly trivial on
`G`.  Drop the kernel claim and the quotient is simple but not finitely
presented — that is exactly the dead route
`boone-higman-via-maximal-quotient-of-the-envelope`.  Drop
the Tietze equivalence and finite normal generation of `M` does not convert
into a finite presentation of the quotient.

Four of the five are established.  The route is one open claim wide, and that
claim is a statement about the normal lattice of an explicitly presented
elementary matrix group.

## What the route does not deliver

No uniformity.  The choice of `M` is by Zorn and is not computable from a
presentation of `G`, so even if this route closes, it produces no algorithm
sending a group to a finite presentation of a simple envelope.  That is
consistent with the conjecture, which is purely existential, and it is worth
stating because a reader expecting an effective construction from a
"constructive-looking" chain of embeddings will not find one here.
