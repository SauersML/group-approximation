---
rg: 2
id: random-groups-below-density-half-contain-surface-subgroups
kind: claim
title: Random groups at density below one half contain quasiconvex surface subgroups with overwhelming probability
distinct_from:
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for every one-ended hyperbolic group; this holds with overwhelming probability in Gromov's density model only.
---

A random group in Gromov's density model at any density `D < 1/2` contains a
quasiconvex surface subgroup with probability `1 - O(e^{-n^c})`.

D. Calegari and A. Walker, *Random groups contain surface subgroups*,
arXiv:1304.2188. TeX source `random_groups.tex`, fetched on MSI 2026-09-13.

- **Density model** (Definition, l.139--147), verbatim: "A random $k$-generator
  group at density $D$ (for some $0<D<1$) and at length $n$ is a group defined by a
  presentation $G:=\langle x_1,\cdots, x_k \; | \; r_1,\cdots, r_\ell \rangle$ where
  $\ell = (2k-1)^{Dn}$, and where the $r_i$ are chosen randomly (with the uniform
  distribution) and independently from the set of all cyclically reduced cyclic
  words of length $n$ in the $x_i^{\pm}$."
- **Theorem** `theorem:surface_random_group` (l.2524--2528), verbatim:

  > A random group of length $n$ and density $D<1/2$ contains a surface subgroup
  > with probability $1-O(e^{-n^c})$. In fact, it contains $O(e^{n^c})$ surfaces of
  > genus $O(n)$. Moreover, these surfaces are quasiconvex.

- **Few relators model** (Theorem `theorem:surface_one_relator`, l.2356--2359): a
  random one-relator group `<F_k | r>` with `r` a random cyclically reduced word of
  length `n` contains a surface subgroup with probability `1-O(e^{-n^c})`.

The paper (l.160) records Gromov's dichotomy: above density `1/2` random groups are
trivial or `Z/2Z`, below it they are infinite and hyperbolic. So the theorem covers
every density at which the question is nontrivial in this model.
