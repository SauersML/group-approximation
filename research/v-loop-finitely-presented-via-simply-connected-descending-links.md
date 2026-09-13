---
rg: 2
id: v-loop-finitely-presented-via-simply-connected-descending-links
kind: route
title: "V_loop is finitely presented if the loop braid descending links are eventually simply connected"
target: loop-braided-thompson-group-v-loop-is-finitely-presented
requires:
  - loop-braid-groups-are-type-f-infinity
  - loop-braid-cloning-system-is-properly-graded
  - loop-braid-descending-links-are-eventually-simply-connected
---

Witzel–Zaremsky, arXiv:1405.5491v3, Proposition 5.9, verbatim: "Let G∗ be
equipped with a properly graded cloning system. If G_k is eventually of type
F_n and L_k(G∗) is eventually (n − 1)-connected then T(G∗) is of type F_n."

Take n = 2 and `G_* = LB_*`:

- `LB_k` is of type F∞, hence F_2;
- the system is properly graded;
- `L_k(LB_*)` is eventually 1-connected.

So `V_loop` is of type F_2, i.e. finitely presented.
