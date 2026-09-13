---
rg: 2
id: lo-simple-type-f-via-thompson-like-subgroups
kind: route
title: Reach a left-orderable simple group of type F through Thompson-like subgroups or disjoint supports (dead)
target: some-left-orderable-simple-group-has-type-f
requires:
  - some-lo-simple-type-f-group-contains-thompson-like-subgroups
---

**Dead.** If some left-orderable simple group of type F has Thompson-like subgroups, then a
left-orderable simple group of type F exists. The implication is trivially valid, but its premise is
refuted.

This is the Thompson-like upgrade route for Zaremsky Problem 1.22. It covers:
- making the Hyde–Lodha groups, or overgroups of them, of type F;
- building simple overgroups of `F'`, chain groups or locally moving groups of homeomorphisms;
- using actions on the line with arbitrarily many disjointly supported elements.

Invalidated by `finite-cd-line-groups-bound-disjointly-supported-families`, whose items 1–2 force infinite
cohomological dimension on every such group. The route requires its own refuted premise, so it cannot
fire even without the invalidation.
