---
rg: 2
id: faithful-continuous-normal-form-for-infinite-fg-groups
kind: claim
title: Every infinite finitely generated group has a set of normal forms whose boundary carries a faithful continuous action
distinct_from:
  literal-group-structural-normal-form: that is a normal form for one specific group constructed in this repository, used to decide its word problem; this is a universal existence statement over all infinite finitely generated groups and its content is the boundary dynamics, not decidability.
  countable-group-embeds-in-two-generator-simple-group: that embeds groups into simple groups; this constructs a language of normal forms and a boundary action for a group given as it stands, and embeds nothing.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
  - research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md
---

Let `G` be an infinite finitely generated group.  Then there are a finite
symmetric monoid generating set `X` and a set `L ⊆ X*` containing exactly one
word representing each element of `G`, such that the left multiplication
action of `G` on `L` extends continuously to `L ∪ ∂L`, where `∂L ⊆ X^ω` is
the set of accumulation points of `L`, and the induced action

    G  acting on  ∂L

is faithful.  Indeed `∂L` is `G`-equivariantly homeomorphic to the Bernoulli
shift `{0,1}^G`.

The language `L` is **not** claimed regular, automatic, or effective.

## Provenance and what is deliberately not claimed

This came out of the 2026-08-17 Boone--Higman resolution attempt as a side
observation, where it is presented as answering a question left open in a
preliminary manuscript of Belk--Bleak--Chatterji--Matucci--Perego, *Rational
embeddings of continuous automatic groups* — their Remark 1.2, asking whether
every infinite finitely generated group admits a continuous normal form with
faithful boundary action.

**That reading is unverified and this node does not assert it.**  The
preprint is real — it is listed on Matucci's publication page as a
preliminary 2026 collaboration — but no public text was reachable on
2026-08-17, so neither Remark 1.2 nor the paper's definition of a continuous
language of normal forms could be read.  See
`research/artifacts/boone-higman-audit-2026-08-17.md` §A.4.  The statement
above is therefore phrased self-containedly, with every term defined in it,
so that its truth does not depend on matching an unread definition.  If that
definition additionally requires regularity of `L`, the construction does not
meet it and the claim is still true as stated.

## Why it is here and why it is parked

It is a correct theorem produced by an audited attempt, and this graph is
where such things go.  It feeds no route.  Nothing in
`boone-higman-conjecture` or any of its four live routes touches it, and it
should not be read as evidence about any of them.

The reason it does not help: the padding construction produces a language
with no finite-state structure whatsoever, so it does not show any group is
continuous automatic and it does not activate the rational-embedding
machinery those authors build.  For a group with solvable word problem much
of the construction can be made effective — enumerate the group, choose
canonical representatives, build the dense Bernoulli configuration
recursively — but "recursive" is very far from "regular", and no way was
found to compress the language into a finite automaton while keeping the
full-shift boundary.

## Source check (bh-free-21, 2026-09-18)

The preprint is now publicly readable:
`https://jimbelk.github.io/web/RationalEmbeddingsContinuousAutomaticPreliminary.pdf`, preliminary
version, read in full through p. 8. Record in
`research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md` §1.

- **The question.** Remark 1.2 (p. 3) reads: "We do not know whether every infinite, finitely
  generated group G has a continuous normal form L such that G acts faithfully on ∂L."
- **The definitions match this node's statement.**
  - A language of normal forms (p. 3): one word per element over a finite symmetric generating
    set.
  - It is continuous (p. 3) if the natural left action extends to a continuous action on
    `L ∪ ∂L`.
  - The continuity criterion is over monoid generators (Prop. 1.3 = Prop. 2.1). The proof route's
    Step 5 is exactly that check.
  - Neither regularity nor automaticity is part of the definition.
- **So the reading is verified.** This node answers the question of Remark 1.2 affirmatively, in
  its literal form. The authors' interest is in automatic normal forms (their §1.1 and
  Cor. 1.9), and the padded language here is not regular. So the answer is literal only, and it
  is recorded that way. It is a preliminary version, so the remark's numbering or wording may
  change. No priority is claimed.
