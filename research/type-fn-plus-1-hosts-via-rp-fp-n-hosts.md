---
rg: 2
id: type-fn-plus-1-hosts-via-rp-fp-n-hosts
kind: route
title: "Recursively presented FP_{n+1} hosts give F_{n+1} hosts for groups of type F_n"
target: every-type-fn-group-embeds-in-a-type-fn-plus-1-group
requires:
  - every-fg-rp-group-has-rp-fp-n-hosts-for-each-finite-n
  - fournier-facio-zaremsky-rp-fp-n-hosts-give-f-n-hosts
---

Let `n >= 2` and let `G` be of type `F_n`, so `G` is finitely presented. The
first required claim at level `n+1` is the hypothesis of Theorem A of
Fournier-Facio--Zaremsky at level `n+1`. Theorem A then gives an embedding of
every finitely presented group, in particular `G`, into a group of type
`F_{n+1}`.
