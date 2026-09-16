---
rg: 2
id: torsion-free-virtually-free-by-cyclic-groups-have-gd-two
kind: claim
title: Torsion-free virtually free-by-cyclic groups have geometric dimension two
distinct_from:
  eilenberg-ganea-conjecture: that is EG for every group of cd 2; this is the special case of torsion-free finite extensions of free-by-cyclic groups, whose cd is at most 2 by Serre's theorem.
  virtually-rfrs-cd2-coherence-characterization: that characterizes virtual free-by-cyclicity for virtually RFRS groups; this asks whether the torsion-free groups in that class have 2-dimensional classifying spaces.
artifacts:
  - research/artifacts/eg-special-case-virtually-free-by-cyclic-2026-09-16.md
---

Every torsion-free group `G` with a finite-index subgroup `F ⋊ Z`, where `F` is free of any
rank, has a 2-dimensional `K(G,1)`.

`cd G ≤ 2` by Serre's theorem, so this is the Eilenberg--Ganea conjecture for the class. The
free-by-cyclic subgroup has an obvious 2-dimensional `K(π,1)`, a mapping torus of a graph map.
The open problem is the finite extension.

**Why it matters.** Combined with `virtually-rfrs-cd2-coherence-characterization` (FLSP,
arXiv:2603.16763 Corollary 4.1), this gives EG for every finitely generated virtually RFRS
torsion-free group of cd 2 that is coherent, equivalently has `b_2^(2) = 0`.

**Status of the pieces.**
- `virtually-free-by-cyclic-normal-fibre-gives-gd-two` covers:
  - every such `G` in which some free fibre of a finite-index subgroup is normal in `G`, for
    example when `b_1(H) = 1` or there is an invariant fibration with free kernel;
  - every torsion-free virtually `F_n × Z` group.

## Attempts

1. **Hi-spec lane, 2026-09-16.** Proved the two cases above, via
   `free-by-virtually-cyclic-torsion-free-groups-have-gd-two`. The residual case has, for every
   fibration `H → Z` with free kernel (`H ⊲ G`), a `G`-conjugate that is not `±` itself, and
   non-periodic monodromy.
   - Intersecting the orbit of kernels gives a free normal `N` with `G/N` virtually `Z^r`,
     `r ≥ 2`. That quotient has no tree action with finite stabilizers, and the same
     construction gives only `gd ≤ r + 1`.
   - Averaging needs an invariant fibred component.
   - Coinduction has dimension `2[G:H]`.
   - The L²/Kaplansky criterion reduces the finite version to a deficiency-1 presentation of
     `G`, with no control.

   Details are in the artifact, §4, and in
   `notes/eilenberg-ganea-conjecture-special-case-swarm-2026-09-16.md`.
