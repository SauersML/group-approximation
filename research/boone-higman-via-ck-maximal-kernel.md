---
rg: 2
id: boone-higman-via-ck-maximal-kernel
kind: route
title: Build the marked Steinberg cover and finitely normally generate one maximal kernel
target: boone-higman-conjecture
requires: [boone-higman-thompson-simple-envelope, clapham-fp-embedding-preserves-word-problem, fp-group-embeds-in-fp-derived-subgroup, ck-steinberg-marked-cover, proper-normal-subgroups-miss-the-normally-generating-core, ck-envelope-has-a-finitely-normally-generated-maximal-kernel, fp-quotient-iff-kernel-finitely-normally-generated]
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Let `G` be finitely generated with solvable word problem.

By `boone-higman-thompson-simple-envelope`, applied to `G × Z` so that the
core comes out infinite, embed `G <= S` with `S` finitely generated,
computably presented, infinite and simple. Pick `1 != s in S`. Its word
problem is decidable by dovetailing enumeration of relator consequences
with witnesses that a fixed nonidentity word lies in the normal closure
of the tested word. Clapham embeds `S` in a finitely presented group `H`.
By `fp-group-embeds-in-fp-derived-subgroup`, embed `H` in `[T,T]` with
`T` finitely presented. Apply `ck-steinberg-marked-cover` with this marking
and `g=s`. This gives a finitely presented `Gamma >= H >= S` with
property (T) and `Gamma = <<s>>_Gamma`, as a marked cover of `EL_4(U)`.

By `ck-envelope-has-a-finitely-normally-generated-maximal-kernel` choose a
maximal proper normal `M <| Gamma` that is finitely normally generated.
Maximality makes `Gamma/M` simple.  By
`proper-normal-subgroups-miss-the-normally-generating-core`, `M ∩ S = 1`, so
`S` — and therefore `G` — embeds in `Gamma/M`.  By
`fp-quotient-iff-kernel-finitely-normally-generated`,
`Gamma/M` is finitely presented.

So `G` embeds in a finitely presented simple group.

## Why every prerequisite is genuinely used

The Thompson envelope supplies the simple core. Clapham and the finite
derived-subgroup embedding supply the finitely presented marking needed by
the Steinberg-cover construction. That construction supplies the finitely
presented ambient group and normal generator. Drop the
core-survival lemma and a maximal quotient is simple but possibly trivial on
`G`.  Drop the kernel claim and the quotient is simple but not finitely
presented — that is exactly the dead route
`boone-higman-via-maximal-quotient-of-the-envelope`.  Drop
the Tietze equivalence and finite normal generation of `M` does not convert
into a finite presentation of the quotient.

All prerequisites except the maximal-kernel claim are established.
The route is one open claim wide, and that
claim is a statement about the normal lattice of a finitely presented
marked cover. [[ck-steinberg-marked-cover]] supplies an explicit Steinberg
source for that cover. Finite presentation of the elementary image itself
has not been established, so it cannot replace the cover in this criterion.

## What the route does not deliver

No uniformity.  The choice of `M` is by Zorn and is not computable from a
presentation of `G`, so even if this route closes, it produces no algorithm
sending a group to a finite presentation of a simple envelope.  That is
consistent with the conjecture, which is purely existential, and it is worth
stating because a reader expecting an effective construction from a
"constructive-looking" chain of embeddings will not find one here.
