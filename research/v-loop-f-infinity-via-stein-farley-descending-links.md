---
rg: 2
id: v-loop-f-infinity-via-stein-farley-descending-links
kind: route
title: "V_loop is F_infinity if the loop braid cloning system is properly graded with increasingly connected descending links"
target: loop-braided-thompson-group-v-loop-is-type-f-infinity
requires:
  - loop-braid-groups-are-type-f-infinity
  - loop-braid-cloning-system-is-properly-graded
  - loop-braid-descending-links-are-increasingly-connected
---

Witzel–Zaremsky, arXiv:1405.5491v3, Proposition 5.9 (p. 31), verbatim: "Let
G∗ be equipped with a properly graded cloning system. If G_k is eventually of
type F_n and L_k(G∗) is eventually (n − 1)-connected then T(G∗) is of type F_n."

Apply it to `G_* = LB_*`, for every n:

- `loop-braid-groups-are-type-f-infinity` gives the finiteness input;
- `loop-braid-cloning-system-is-properly-graded` gives the grading hypothesis;
- `loop-braid-descending-links-are-increasingly-connected` gives, for each n,
  an index beyond which `L_k(LB_*)` is (n−1)-connected.

So `V_loop = T(LB_*)` is of type F_n for every n, hence of type F∞.

The proof of Proposition 5.9 in the source uses:
- the contractible Stein–Farley complex (Proposition 4.8);
- cell stabilizers that are finite-index subgroups of the `G_k` (Lemma 4.9,
  which needs proper grading);
- cocompact sublevel sets (Lemma 5.5);
- the identification of descending links with `L_k(G_*)` (Observation 5.8);
- Brown's criterion in the form of Corollary 5.4.
