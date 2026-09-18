---
rg: 2
id: sl2-q-duplicate-ids-agree
kind: route
title: The duplicate id sl-2-q-embeds-in-fp-simple-group states the same claim as sl2-q-embeds-in-fp-simple-group
target: sl2-q-embeds-in-fp-simple-group
requires:
  - sl-2-q-embeds-in-fp-simple-group
---

The two claims have the same statement: `SL_2(Q)` embeds in a finitely
presented simple group. They were landed independently, 90fb10146 and
39b37d26f. This route and `sl-2-q-duplicate-ids-agree` tie them together, so
a proof of either establishes both.
