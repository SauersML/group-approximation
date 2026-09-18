---
rg: 2
id: all-hyperbolic-groups-lie-in-one-fp-simple-group
kind: claim
title: One finitely presented simple group contains every hyperbolic group
distinct_from:
  hyperbolic-groups-satisfy-boone-higman: that gives each hyperbolic group its own finitely presented simple host (BBMZ); this asks for one host for all of them at once.
  one-fp-simple-group-contains-every-brin-thompson-subgroup: that is an unconditional common host for the groups in some nV, which covers the cubulated hyperbolic groups; this is the whole hyperbolic class.
---

**OPEN.** There is a finitely presented simple group containing a copy of every
word-hyperbolic group.

- **Known part.** Every hyperbolic group acting properly and cocompactly on a CAT(0)
  cube complex lies in the host of `one-fp-simple-group-contains-every-brin-thompson-subgroup`
  (indeed in `2V`).
- **Sufficient conditions.**
  - Zaremsky Problem 2.19(a), `every-hyperbolic-group-embeds-in-some-brin-thompson-group`,
    via route `all-hyperbolic-groups-one-fp-simple-host-via-nv`.
  - Boone–Higman, by `common-decidable-hosts-iff-uniform-word-problem`. The finite
    presentations of hyperbolic groups form a c.e. class with uniformly solvable word
    problem: Papasoglu's algorithm halts exactly on hyperbolic presentations and
    certifies a Dehn presentation (cited, not re-read here).
- **Obstacle.** Infinite hyperbolic groups with property (T). They lie in no RAAG
  virtually, so the cubulated method misses them, and BBMZ's hosts are built one
  group at a time from each group's own boundary action.
- **No hyperbolic host.** A finitely generated group containing every hyperbolic group
  contains every finite group, while a hyperbolic group has finitely many conjugacy
  classes of finite subgroups, so the host cannot itself be hyperbolic.
