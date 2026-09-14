---
rg: 2
id: countable-transitive-decoder-fiber-from-gottschalk
kind: route
title: Surjunctivity makes the decoder an inverse with singleton fibers
target: injective-ca-admit-countable-transitive-decoder-fiber
requires:
  - gottschalk-surjunctivity-conjecture
artifacts:
  - research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md
---

If every group is surjunctive, every injective automaton `tau` over a finitely
generated infinite group is bijective. Its inverse is continuous and commutes
with the shift, so it is a cellular decoder `sigma` with `sigma tau = id` whose
fibers are all singletons. The group is countable, so a configuration with dense
orbit exists, and its fiber is countable.

This is the converse of `gottschalk-via-countable-transitive-decoder-fiber`. The
two routes form a cycle on purpose. The prerequisite of that route is
equivalent to the goal, so that route is an exact reformulation, not a
weakening. Do not delete either route to silence the cycle warning. Section 1 of
the artifact gives the check of both directions.
