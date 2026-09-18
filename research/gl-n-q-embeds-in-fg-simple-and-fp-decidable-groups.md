---
rg: 2
id: gl-n-q-embeds-in-fg-simple-and-fp-decidable-groups
kind: claim
title: GL_n(Q) embeds in a finitely presented group with solvable word problem and in a finitely generated simple group with solvable word problem
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that asks for one host that is finitely presented AND simple; this gives each adjective separately, which is known, and so locates the open part of the root exactly.
  boone-higman-thompson-simple-envelope: that is the Boone--Higman--Thompson envelope for finitely generated inputs; this applies it to the countable, non-finitely-generated group GL_n(Q) through a two-generated decidable overgroup.
  clapham-fp-embedding-preserves-word-problem: that is Clapham's theorem for finitely generated inputs; this is its consequence for GL_n(Q).
  rational-linear-groups-satisfy-boone-higman: that gives finitely presented simple hosts for the finitely generated subgroups of GL_n(Q) separately; this gives single hosts for the whole group, each missing one adjective.
---

**ESTABLISHED** by `gl-n-q-embeds-in-fg-simple-and-fp-decidable-groups-proof`
(assembly of cited theorems; not independently reviewed; no novelty claimed).

## Statement

For every `n >= 1` there are:

1. a **two-generated** group `G*` with solvable word problem containing `GL_n(Q)`;
2. a **finitely presented** group with solvable word problem containing `GL_n(Q)`;
3. a **finitely generated simple** group with solvable word problem containing
   `GL_n(Q)`, for example the Belk--Zaremsky group `G* V_(G*)`;
4. a **finitely presented** group `P` with a **simple** subgroup `S` such that
   `GL_n(Q) <= S <= P`.

So the root `gl-n-q-embeds-in-fp-simple-group` asks for exactly one thing that
is not already known: a single host that is finitely presented and simple at
once. Item (2) is stated verbatim in the survey (Proposition 3.3(2)); the other
items are the survey's general theorems applied to `G*`.

## Consequences for the root (the inverter's reading)

- **The negation is a Boone--Higman counterexample with named witnesses.** If
  the root fails for some `n`, then every finitely generated group with solvable
  word problem containing `GL_n(Q)`, in particular `G*` of item (1) and the
  finitely presented group of item (2), embeds in no finitely presented simple
  group. So `boone-higman-conjecture` fails for a finitely presented group.
- **The two adjectives are already achieved by standard envelopes.** The simple
  envelope of item (3) is built from the translation action of `G*` on itself,
  and the survey notes (sentence after Theorem 4.15) that "the action of an
  infinite group G on itself by translation never has finitely many orbits of
  pairs, so the examples of the form GV_G are not useful in this context". So
  the finite-presentation criterion of Theorem 4.15 never applies to item (3);
  a proof of the root needs a different action of an overgroup of `GL_n(Q)`
  (compare `gl-n-q-in-permutational-boone-higman-class`).

## Attempts

None beyond the assembly above.
