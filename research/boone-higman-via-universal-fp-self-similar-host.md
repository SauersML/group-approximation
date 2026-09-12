---
rg: 2
id: boone-higman-via-universal-fp-self-similar-host
kind: route
title: Dead - embed every decidable group in a finitely presented self-similar group and apply Zaremsky
target: boone-higman-conjecture
requires:
  - every-decidable-group-embeds-in-fp-self-similar-group
  - fp-self-similar-groups-embed-in-fp-simple-groups
---

**Dead.** Invalidated by `self-similar-hosts-contain-only-residually-finite-groups`,
and its first premise is refuted.

The composition itself would be immediate. Embed the input in a finitely
presented self-similar group, then apply Zaremsky's Theorem 1.1 and restrict.
The premise fails for every input that is not residually finite, Thompson's V
among them. So the method reaches only residually finite inputs, where it is
the route `fp-rf-boone-higman-via-fp-self-similar-overgroups`.
