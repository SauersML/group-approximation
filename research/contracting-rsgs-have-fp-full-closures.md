---
rg: 2
id: contracting-rsgs-have-fp-full-closures
kind: claim
title: The full closure of a contracting RSG is a full contracting RSG with the same nucleus, hence finitely presented, so Question 1.4 holds for contracting inputs
distinct_from:
  contracting-rsgs-embed-in-fp-simple-groups: that imports BBMZ Theorem B for full contracting RSGs; this observes that the full closure of any contracting RSG is again contracting, so Theorem B applies to it.
  fp-rsgs-have-fp-full-closures: that is the open question for all finitely presented RSGs; this is its contracting case, with no finite presentation hypothesis on the input.
---

**ESTABLISHED** through `contracting-rsgs-have-fp-full-closures-proof`. Lane proof
(bh-higman-classic), elementary, not independently reviewed. No priority claimed; BBMZ may
regard it as evident.

## Statement

Let `G ≤ R_{Γ,E}` be an RSG. Then:
1. `[[G]] ≤ R_{Γ,E}`, `[[G]]` is a full RSG, and `N_{[[G]]} = N_G`.
2. If `G` is contracting, then `[[G]]` is a full contracting RSG, so it is finitely presented
   by BBMZ Theorem B (`contracting-rsgs-embed-in-fp-simple-groups`, item 4). It also embeds in
   a finitely presented simple group (item 5).

So Question 1.4 (`fp-rsgs-have-fp-full-closures`) holds for every contracting RSG, finitely
presented or not. A counterexample must be non-contracting.
