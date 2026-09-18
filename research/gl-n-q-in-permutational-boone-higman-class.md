---
rg: 2
id: gl-n-q-in-permutational-boone-higman-class
kind: claim
title: For every n >= 2 the group GL_n(Q) embeds in a finitely presented group with an action of type (A)
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that asks only for a finitely presented simple overgroup; this asks for the permutational form, which implies it and is implied by it whenever the simple host itself lies in B_A.
  char-zero-linear-groups-satisfy-permutational-boone-higman: that puts every finitely generated linear group in characteristic zero into B_A; this is the countable group GL_n(Q), which lies in no finitely generated linear group and is not reached by any local-to-global step.
  permutational-boone-higman-conjecture: that is the universal statement for finitely generated groups with solvable word problem; this is one named countable input.
  permutational-host-forms-agree-for-countable-inputs: that gives the equivalent host forms for any input; this is the open membership question for GL_n(Q).
---

**OPEN.** For every `n >= 2` there are:
- a finitely presented group `Γ`;
- a faithful action of `Γ` on a set `S` with finitely generated point
  stabilizers and finitely many orbits of two-element subsets;
- an injective homomorphism `GL_n(Q) -> Γ`.

In other words `GL_n(Q) ∈ B_A`, the permutational Boone--Higman class of
Belk--Fournier-Facio--Hyde--Zaremsky.

## Why this is the target to aim at

- **It suffices for the root.** Route `gl-n-q-bh-via-permutational-class`, via
  Zaremsky's Corollary B.
- **It is the weakest target within twisted Brin--Thompson envelopes.**
  - The finiteness conditions can only be relaxed by dropping faithfulness, and
    `permutational-host-forms-agree-for-countable-inputs` shows that gains
    nothing.
  - Nothing in that node requires `GL_n(Q)` to be finitely generated or to have a
    solvable word problem.
- **The root gives it back for every host of the known kinds.** If `GL_n(Q)`
  embeds in a finitely presented simple group `S` lying in `B_A`, then
  `GL_n(Q) ∈ B_A`. Examples of such `S`:
  - any finitely presented simple group with a faithful highly transitive action
    (BFFHZ universality);
  - any finitely presented simple group of Cantor homeomorphisms containing the
    commutator subgroup of a Higman--Thompson group;
  - any finitely presented twisted Brin--Thompson group.

  Whether the root implies this claim for an arbitrary host is the `GL_n(Q)`
  case of the question whether BH implies PBH
  (`bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`).

## Equivalent and sufficient forms

By `permutational-host-forms-agree-for-countable-inputs` and
`gl-n-q-targets-are-cofinal-in-n`, each of the following is equivalent to the
claim:

- **(a) Finitary-alternating host.** A finitely presented `Γ ≤ Sym(X)` with
  `X` infinite, `Alt_fin(X) ≤ Γ` and `GL_n(Q) ≤ Γ`, for every `n`. This is the
  form for Houghton-type constructions.
- **(b) Simple host in `B_A`.** An embedding of `GL_n(Q)` in a finitely
  presented simple group that lies in `B_A`, for example in a finitely
  presented simple group of Cantor homeomorphisms containing `V'_(d,r)`.
- **(c) Any infinite set of `n`.** The same for infinitely many `n` only, or for
  `SL_n(Q)` or `PGL_n(Q)` in place of `GL_n(Q)`. The group `PGL_n(Q)` acts
  faithfully and 2-transitively on `P^(n-1)(Q)`.

The following suffice:

- **(d) Finite index.** Any finite-index subgroup of `GL_n(Q)`, or of a group
  containing it, in `B_A`.
- **(e) Pieces.** Embeddings into finite direct or free products of
  `B_A`-groups (`boone-higman-type-a-class-closed-under-finite-extensions`).

## What does not reduce to it

- **Finitely generated subgroups.** Every finitely generated subgroup of
  `GL_n(Q)` is already in `B_A`
  (`char-zero-linear-groups-satisfy-permutational-boone-higman`). That does not
  give this claim: the claim needs a single host.
- **Residually finite hosts.** By obstruction O1 of the root, `Γ` is never
  residually finite, and neither is any intermediate overgroup.
- **The case `n = 1`.** `GL_1(Q)` and `(Q,+)` are in `B_A`, through
  `VA`. That is recorded in the equivalence node.

## Attempts

None yet. The construction lanes of the gq swarm aim at forms (a)–(c).
