---
rg: 2
id: countable-group-embeds-in-two-generator-simple-group
kind: claim
title: Every countable group embeds in a two-generator simple group
distinct_from:
  kl-counterexample-can-be-two-generator-simple: that is the reduction this embedding theorem is used to prove, and it is about Kervaire--Laudenbach counterexamples; this is the classical embedding statement, with no equation in it, and it would stand if the conjecture were settled either way.
  kl-holds-over-two-generator-simple-groups: that is the conjecture restricted to simple coefficient groups and is open; this is a classical embedding theorem about the same class of groups and says nothing about equations over them.
  boone-base-group-two-generator-one-relator: that identifies one specific split-extension base group as a one-relator group on a fixed generating set; this is a universal embedding statement into simple groups, shares only the word "generator", and neither uses nor implies anything about that presentation.
  simple-sofic-total-mf-radical: that asks for a countable simple sofic group with total MF radical -- an approximation property of one constructed group; this asserts that every countable group sits inside some two-generator simple group, with no approximation content at all.
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Every countable group embeds in a two-generator nonabelian simple group.

Classical: Schupp, *Embeddings into simple groups*, J. London Math. Soc. (2)
**13** (1976) 90--94.

**Verification status.**  Not re-read from the publisher on 2026-08-17; the
statement and reference are transcribed from the external audit
(`research/artifacts/kervaire-laudenbach-audit-2026-08-17.md` §A).  It is not
in doubt, but it is the one input of the reduction chain that this session
did not read from source, so it is recorded separately rather than folded
into the route that uses it.

**Robustness of the use made of it.**  Only *nonabelian simple* is consumed
downstream, by `kl-simple-failure-leaves-only-the-cyclic-quotient`.  The
two-generator refinement is carried because it is what the classical theorem
gives, and it makes the reduced problem concrete, but no node depends on it:
were the refinement to fail, `kl-counterexample-can-be-two-generator-simple`
would weaken to "simple" and every downstream statement would stand
unchanged.
