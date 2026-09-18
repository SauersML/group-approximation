---
rg: 2
id: every-cocf-group-is-exact
kind: claim
title: Every finitely generated group with context-free co-word problem is exact; this implies Thompson's V is exact, and under Lehnert's conjecture it is equivalent to exactness of V
distinct_from:
  lehnert-conjecture-every-cocf-group-embeds-in-v: that is the embedding conjecture for coCF groups; this is an analytic property of the whole class, and Lehnert's conjecture is what makes it equivalent to one statement about V.
  fp-simple-nonexact-group: that asks for any non-exact finitely presented simple group; a refutation of this claim through a subgroup of V would settle that one, since V is finitely presented and simple, but a refutation outside V would not.
---

**OPEN.** Every finitely generated group whose co-word problem is a context-free language
has property A (is exact).

## Relation to V

- **This claim implies that `V` is exact.** `V` is itself finitely generated and coCF
  (Lehnert--Schweitzer, arXiv:math/0507090, as recorded in
  `lehnert-conjecture-every-cocf-group-embeds-in-v`).
- **Every non-exact finitely generated subgroup of `V` is coCF.** coCF passes to
  finitely generated subgroups (Holt--Rees--Röver--Thomas; cited, not re-read). So a proof
  that `V` is **not** exact must produce a non-exact coCF group.
- **Under Lehnert's conjecture, this claim is equivalent to exactness of `V`.** If every
  coCF group embeds in `V`, then exactness of `V` passes to all of them, since exactness
  passes to subgroups (`exact-groups-are-closed-under-extensions`). The conjecture's
  statement was read at source in Bishop--Bodart--Issini--Perego, arXiv:2601.13058, §0:
  "A finitely generated group $G$ is co-context-free if and only if it embeds in Thompson
  group $V$."

## Relation to the graphical test case

- **Expander-type inputs never embed in `V`.** `V` has the Haagerup property
  (`thompson-v-has-haagerup-property`), so it contains no group with a weakly embedded
  expander (`haagerup-hosts-carry-no-weak-expander`). In particular it does not contain
  the decidable `G_exp` of `decidable-graphical-non-exact-groups-exist`.
- **The a-T-menable non-exact `G_PW` of the same node is the natural candidate.** For it
  to embed in `V`, it must be coCF. Whether any graphical small cancellation presentation
  with infinitely many components gives a coCF group is not known here.
  - Every coCF group has word problem decidable in cubic time (context-free recognition),
    and its torsion orders are bounded by a function of word length
    (`cocf-group-torsion-order-bounded-by-word-length`).
  - So a candidate needs a polynomial-time word problem. The brute-force Osajda labellings
    do not supply one.
