---
rg: 2
id: strict-pairs-admit-post-surjective-decoders
kind: claim
title: A group carrying a strict automaton pair carries one whose decoder is post-surjective
distinct_from:
  post-surjective-decoders-convert-strict-pairs-to-dual-failures: that proves what a post-surjective decoder gives and when decoders are post-surjective; this asks for the missing existence step for arbitrary nonlinear strict pairs.
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

**OPEN.** Suppose `G` carries an injective, non-surjective automaton over some
finite alphabet. Then `G` carries a strict pair `(τ, σ)`, over some possibly
different finite alphabet, whose decoder `σ` is post-surjective.

**What is proved** (`post-surjective-decoders-convert-strict-pairs-to-dual-failures`):
- **(b)** every decoder is post-surjective at configurations asymptotic to the image `Y` of the encoder;
- **(c)** affine decoders over abelian alphabets are post-surjective;
- **(e)** configurations carrying a Garden-of-Eden pattern of the encoder infinitely often are never asymptotic to `Y`.

So the whole difficulty sits at configurations with infinitely many
Garden-of-Eden occurrences. There the decoder's local rule off the language
of `Y` is free, and a proof must choose it so that finite output changes lift
to finite input changes.

**Consequence.** With the conversion claim this gives
`dual-surjunctive-groups-are-surjunctive`. Over any dual surjunctive group,
including every sofic group, no strict pair has a post-surjective decoder.
