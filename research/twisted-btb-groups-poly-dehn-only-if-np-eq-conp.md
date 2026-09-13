---
rg: 2
id: twisted-btb-groups-poly-dehn-only-if-np-eq-conp
kind: claim
title: A finitely presented twisted Brin-Thompson group on an infinite set has polynomially bounded Dehn function only if NP = coNP
distinct_from:
  twisted-brin-thompson-wp-equals-actor-orbit-problem: that bounds the word problem of SV_G by its actor's orbit problem in both directions; this is a lower bound on the Dehn function that holds for every actor at once, because SV_G contains 2V.
  quantitative-higman-embedding-with-dehn-control: that embeds a time-bounded input into some finitely presented group with controlled Dehn function; this shows twisted Brin-Thompson groups on infinite sets can never be such hosts with polynomial control unless NP = coNP.
  np-word-problem-groups-embed-in-fp-simple-polynomial-dehn-groups: that is the open problem of simple polynomial-Dehn hosts for inputs with word problem in NP; this rules out one family of candidate hosts for it.
artifacts:
  - research/artifacts/simple-bors-2026-09-13.md
---

**ESTABLISHED** by `twisted-btb-groups-poly-dehn-only-if-np-eq-conp-proof`.

Let `G` act faithfully on an infinite countable set `S`, and suppose the twisted
Brin--Thompson group `SV_G` is finitely presented. If the Dehn function of
`SV_G` has a polynomial upper bound, then `NP = coNP`.

Equivalently: under `NP != coNP`, every finitely presented twisted
Brin--Thompson group on an infinite set has Dehn function above every
polynomial, whatever the actor `G`. This covers every envelope produced through
`twisted-brin-thompson-finite-presentation-criterion` from an action on an
infinite set.

**What it is for.** Twisted Brin--Thompson envelopes are the standard way to
turn type (A) actions into finitely presented simple overgroups. This claim
says they can't give *polynomial* Dehn control, so they can't settle
`np-word-problem-groups-embed-in-fp-simple-polynomial-dehn-groups` unless the
complexity classes collapse.

**Credit and novelty.** This is an immediate corollary of Birget's remark,
arXiv:1902.03852, that `nV` (`n >= 2`) does not embed into a finitely presented
group with polynomially bounded Dehn function unless `NP = coNP`. Belk--Zaremsky
supply the containment `2V <= SV_G`. Nothing beyond recording the consequence
for twisted envelopes is claimed as new.
