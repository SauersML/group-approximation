---
rg: 2
id: rover-nekrashevych-higher-sigma-invariants-are-full
kind: claim
title: If G is a self-similar group of type F_m, every Sigma^m of V_d(G) is the whole character sphere
distinct_from:
  rover-nekrashevych-bnsr-invariants-are-full: that is the candidate answer for every finitely generated G, including groups not of type F_m whose V_d(G) is; this is the higher-invariant statement under the hypothesis that G itself has type F_m.
  rover-nekrashevych-groups-have-full-bns-invariant: that is the proved case m = 1 with no hypothesis beyond finite generation; this is the statement for all m under a finiteness hypothesis on G.
---

**OPEN.** Let `G <= Aut(T_d)`, `d >= 2`, be a self-similar group of type `F_m`. Then `V_d(G)` has type `F_m`, and
`Σ^m(V_d(G)) = S(V_d(G))`. Equivalently, by Bieri–Renz, the kernel `N` of
`V_d(G) -> Hom(V_d(G), R)^*` (the torsion-free abelianization) has type `F_m`.

Special case: finitely generated abelian `G`, for example the binary odometer. There the stabilizer input
`characters-living-on-m-plus-one-factors-lie-in-sigma-m` is not needed, since the relevant kernels in `G^n` are
free abelian. So `Σ^∞(V_2(Z)) = S^0` would follow from `rover-nekrashevych-stein-farley-complex-properties` alone.

## Attempts

- Reduced (lane z1-14-rover-nek, 2026-09-13) to two named inputs by
  `rover-nekrashevych-higher-sigma-full-via-kernel-brown`: the Stein–Farley properties and the all-living product
  case of Meinert's inequality. No other gap is known to this lane.
