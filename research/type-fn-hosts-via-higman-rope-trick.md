---
rg: 2
id: type-fn-hosts-via-higman-rope-trick
kind: route
title: "Dead: the Higman rope-trick container as an F_{n+1} host of a group of type F_n"
target: every-type-fn-group-embeds-in-a-type-fn-plus-1-group
requires: []
---

**Dead route, recorded so the method is not retried.** Proposal: for `G` of
type `F_n` (`n >= 2`) written as `G = F/R`, the rope-trick container
`Hig_ι(G)` of Fournier-Facio--Zaremsky arXiv:2607.21727v1, Definition 1.5,
is a host of type `F_{n+1}`. That container is the HNN extension of `P x G`
along the double `F *_R F`, conjugating `ι x 1` to `ι x π`; it is the device
of Higman's theorem and of Leary's `FP_2` embedding.

Killed by `higman-rope-trick-group-is-never-fp3`, whose `invalidates:` names
this route. A group of type `F_n` that is not of type `F_{n+1}` is infinite
and not free, so `R != 1`. Theorem B then says `H_3(Hig_ι(G); Q)` is
infinite-dimensional, so the container is not of type `FP_3(Q)`, hence not of
type `F_{n+1}` for any `n >= 2`.

House pattern: a recorded dead route has `requires: []` and is killed only by
the established obstruction's `invalidates:` key.
