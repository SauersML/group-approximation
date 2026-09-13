---
rg: 2
id: closed-mcg-no-aut-embedding-via-no-out-embedding
kind: route
title: A closed-surface mapping class group with no Out(F_n) host has no Aut(F_n) host either
target: some-closed-surface-mcg-embeds-in-no-aut-free-group
requires:
  - some-closed-surface-mcg-embeds-in-no-out-free-group
  - aut-free-embeddability-passes-to-finite-index-overgroups
---

Contrapositive of item 3 of `aut-free-embeddability-passes-to-finite-index-overgroups`:
if `MCG(S_g)` embedded in some `Aut(F_n)`, it would embed in `Out(F_{n+1})`.
