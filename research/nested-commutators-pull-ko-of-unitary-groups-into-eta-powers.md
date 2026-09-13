---
rg: 2
id: nested-commutators-pull-ko-of-unitary-groups-into-eta-powers
kind: claim
title: A j-fold nested commutator of maps M -> U(N) pulls every reduced KO-class of U(N) into eta^(j−1)·KO^*(M), for every N
distinct_from:
  rank-two-spin-trapping-blind-to-depth-three-brackets: That proves the eta-per-bracket property for U(2), where Sigma^∞ U(2) is a wedge of spheres and Künneth applies, and concludes spin blindness by Anderson–Brown–Peterson; this proves the property for every U(N) by induction over smash factors, without claiming bordism blindness for N >= 3.
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-part4-2026-09-13.md
---

Let N >= 1 and let M be a closed manifold. Let g_1, ..., g_{j−1}, h: M -> U(N)
be maps, and put f = [g_{j−1}, [..., [g_1, h]...]] (pointwise). Then:

- f^* z lies in eta^{j−1}·KO^*(M) for every z in KO~^*(U(N)). In particular
  f^* z = 0 for j >= 4, since eta^3 = 0 in KO_*.
- f^* x = 0 for every reduced class x in H^*(U(N); Z/2), once j >= 2.

More generally, for every finite based complex X,
(1_X ∧ c_j)^* maps KO^*(X ∧ U(N)) into eta^{j−1}·KO^*(X ∧ U(N)^{∧j}), where
c_j is the j-fold commutator map.

So for every rank N, the KO-characteristic numbers (with reduced
coefficients) of a fourfold commutator vanish, and so do its Stiefel–Whitney
numbers. This node does not prove full blindness of reduced spin bordism
for N >= 3. The peer claim
spin-trapping-blind-to-fourfold-commutators-in-every-rank proves it, by
splitting MSpin_(2) into ko-modules.

Complete argument. Not independently reviewed.
