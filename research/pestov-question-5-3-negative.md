---
rg: 2
id: pestov-question-5-3-negative
kind: claim
title: Negative answer to Pestov's Question 5.3 on essentially free near actions
distinct_from:
  universal-leavitt-el4-nonsofic: That is the nonsoficity of an explicit group; this is the near-action consequence drawn from it through Elek-Szabo, and is a statement about actions rather than about approximation by permutations.
  q3-4-resolved: That is Pestov's Question 3.4, about whether hyperlinear implies sofic, and is the open program goal; this is his Question 5.3, about near actions, and is closed.
artifacts:
  - GroupApproximation/Endpoint/MainResults.lean
---

ESTABLISHED, as a formal corollary.
`Endpoint/MainResults.countable_group_without_essentiallyFreeNearAction_exists`:

    there is a countable group admitting no essentially free, measure-preserving
    near action on a set carrying a finitely additive probability measure on its
    full power set.

The witness is the ambient group of Theorem A, and the mechanism is
`isSofic_of_admitsEssentiallyFreeNearAction` -- the Elek--Szabo direction that
such a near action would make the group sofic -- contradicted by
[[universal-leavitt-el4-nonsofic]].

Recorded because it is a *named open question answered by the development*,
which is the kind of fact the graph exists to hold, and because it is easy to
mistake for the program goal: this is Pestov's Question 5.3, not his Question
3.4.
