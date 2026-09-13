---
rg: 2
id: gjs-countable-groups-have-free-minimal-subflows
kind: claim
title: Every countably infinite group has a free minimal subflow of 2^G (Gao--Jackson--Seward)
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
---

**ESTABLISHED by citation** (`gjs-countable-groups-have-free-minimal-subflows-citation`). S. Gao, S. Jackson and B. Seward,
*Group colorings and Bernoulli subflows*, arXiv:1201.0513 (Memoirs AMS). Read from the arXiv TeX source on MSI on 2026-09-13,
file `chapter01.tex`.

- **Definitions** (`chapter01.tex`, Section `BASIC NOT`): "A subflow of $X$ is called \emph{free} if it consists entirely of
  aperiodic points, and $x \in X$ is called \emph{hyper aperiodic} if $\overline{[x]}$ is free". Also: "a point $x \in X$ is
  \emph{minimal} if $\overline{[x]}$ is minimal". Here aperiodic means trivial stabilizer.
- **Theorem `INTRO PERFDENSE`** (`chapter01.tex` l.156–158): "Let $G$ be a countably infinite group, and let $k > 1$ be an
  integer. If $U \subseteq k^G$ is open and nonempty, then there exists a perfect (hence uncountable) set $P \subseteq U$
  which consists of pairwise orthogonal minimal hyper aperiodic points."

**Consequence used.** For countably infinite `G`, `2^G` contains a minimal hyper aperiodic point `x`, so `cl(G x)` is a free
minimal subflow. It is infinite, and it has no isolated points (a minimal flow with an isolated point is finite), so it is a
Cantor space.
