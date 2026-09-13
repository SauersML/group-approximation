---
rg: 2
id: zaremsky-3-09-braid-groups-self-similar
kind: claim
title: "Zaremsky Problem 3.9 resolved: are braid groups self-similar, and is some residually finite group outside every self-similar group?"
root: true
distinct_from:
  every-fp-rf-group-embeds-in-fp-self-similar-group: that is one possible answer to the second part of this problem, the universal embedding of finitely presented residually finite groups; this is the two-part question itself, whose first part is about braid groups.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3, Problem 9,
verbatim: "(Added 5/18/24) Are braid groups self-similar? More generally, are
there any examples of (say, finitely presented) groups that are residually
finite but don't embed in a (say, finitely presented) self-similar group?"

This claim is the question. It is established only through an answer route,
and every answer route requires an answer to both parts:

- **Part 1 answered and Part 2 yes.** `zaremsky-3-09-by-fp-rf-example` requires
  `braid-group-self-similar-iff-at-most-three-strands` and
  `some-fp-rf-group-embeds-in-no-fp-self-similar-group`.
- **Part 1 answered and Part 2 no.** `zaremsky-3-09-by-universal-fp-host`
  requires `braid-group-self-similar-iff-at-most-three-strands` and
  `every-fp-rf-group-embeds-in-fp-self-similar-group`.

Never write a `requires: []` route into this claim.

## Precise reading

**Self-similar** means a faithful action on the rooted `d`-regular tree `T_d`
for some `d >= 2` whose image is state-closed. This is the definition in
Zaremsky arXiv:2405.09722, and transitivity on the first level is not assumed.
By Dantas–Santos–Sidki (arXiv:2004.08941), such an action is the same as a
finite family of virtual endomorphisms with trivial joint core.

**Part 1.** "Are braid groups self-similar?" is read as the classification of
the `n` for which `B_n` is self-similar. The answer claim is
`braid-group-self-similar-iff-at-most-three-strands`:
- `B_1`, `B_2`, `B_3` are self-similar, established in
  `braid-groups-on-at-most-three-strands-are-self-similar`;
- `B_n` with `n >= 4` is not, in
  `braid-groups-on-four-or-more-strands-are-not-self-similar`.

Both halves passed review (z-verify-groups, landed d228d90964,
`research/artifacts/zp-review-groups-2026-09-13-part2.md` §10). A novelty
check is pending, so no first-answer wording yet.

**Part 2.** "Say, finitely presented" appears twice. The root takes the
strongest reading: a finitely presented residually finite group embedding in no
finitely presented self-similar group. Weaker readings, recorded here because
they are already settled:

- **Finitely generated input, any self-similar host: YES.**
  `cycle-transposition-lef-group-has-no-regular-tree-action` (established) is a
  two-generated residually finite group with polynomial-time word problem and
  elements of every prime order `>= 5`. It acts faithfully on no regular rooted
  tree, so it lies in no self-similar group.
- **Finitely presented residually finite groups that are not themselves
  self-similar, a question about the group rather than its overgroups:**
  - Baumslag's metabelian group
    (`baumslag-char-zero-metabelian-group-is-not-self-similar`, established);
  - the braid groups `B_n` with `n >= 4`
    (`braid-groups-on-four-or-more-strands-are-not-self-similar`).

  Neither excludes embeddings into larger self-similar groups.
- **Strongest reading: OPEN.** It is decided by
  `some-fp-rf-group-embeds-in-no-fp-self-similar-group` versus its negation
  `every-fp-rf-group-embeds-in-fp-self-similar-group`. The negation belongs to
  the Boone–Higman region; do not duplicate that region's open cruxes.

## Attempts

- 2026-09-13 (z3-09 lane):
  - Part 1: `B_3` constructed as a transitive self-similar group on `T_12`.
    The case `n >= 4` goes through the geometric rigidity of injective virtual
    endomorphisms of `B_n / Z(B_n)`.
  - Part 2 (strongest reading): no progress beyond the Boone–Higman region's
    obstruction list. The sufficient mechanism of torsion of infinitely many
    primes is `fp-rf-group-with-unbounded-prime-torsion`.
