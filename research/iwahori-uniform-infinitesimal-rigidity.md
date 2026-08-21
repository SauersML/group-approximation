---
rg: 2
id: iwahori-uniform-infinitesimal-rigidity
kind: claim
title: Compatible representations of the Iwahori amalgam are uniformly infinitesimally rigid
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - experiments/iwahori_linearized_gap.py
distinct_from:
  iwahori-local-global-defect-question: that is Dogon--Vigdorovich's full question, global in the pair; this is only its derivative at compatible points, a linear statement about cocycles.
  iwahori-nielsen-hs-bilipschitz: that controls a specific involution on representation coordinates; this is a lower bound on the Mayer--Vietoris mismatch map for all cocycle pairs.
---

Let `rho` be a congruence representation of `SL_2(Z[1/2]) = V_1 *_B V_2`
(`V_i` the two modular vertex groups, `B = Gamma^0(2)` the Iwahori edge
group) on `C^d`.  For cocycles `c_i in Z^1(V_i, Ad rho)` let

```text
def(c_1, c_2) = max_(b in S_B) || c_1(b) - c_2(sigma b) ||_2
```

be the linearized local defect.  **Claim:** there is `sigma_0 > 0`,
independent of `rho` and `d`, such that for all `(c_1, c_2)` there is a
common `x in M_d` with

```text
max_i || c_i - delta x ||_2  <=  sigma_0^(-1) def(c_1, c_2).            (UIR)
```

Equivalently, the smallest nonzero singular value of the Mayer--Vietoris
mismatch map on `Z^1(V_1) (+) Z^1(V_2)` (whose kernel is the diagonal
coboundaries, because `H^1(SL_2(Z[1/2]), Ad rho) = 0` by property (T;FD))
is bounded below uniformly.

## Attempts

- **Numerics** (`experiments/iwahori_linearized_gap.py`, MSI, 2026-08-21):
  for the permutation representation on `P^1(F_p)`, the kernel is exactly
  the diagonal coboundaries for all `p <= 47`, and the smallest nonzero
  singular value is `0.816, 0.741, 0.711, 0.570, 0.474, 0.408, 0.351,
  0.271, 0.275, 0.300, 0.273, 0.264, 0.253, 0.206` for `p = 3, 5, 7, 11,
  13, 17, 19, 23, 29, 31, 37, 41, 43, 47`.  Slowly decreasing; undecided.
- **Hecke mechanism.**  The two restrictions `H^1(V_i, Ad rho) -> H^1(B, Ad
  rho)` are the degeneracy maps whose trace-composition is the Hecke
  operator `T_2` on `H^1(Gamma(p), C)` (isotypic for `Ad rho`).  With
  Petersson-adjoint restrictions,
  `||res_1 f - res_2 g||^2 = 3||f||^2 + 3||g||^2 - 2 Re <f, T_2 g>`, so
  Deligne's `|a_2| <= 2 sqrt 2` gives the gap `3 - 2 sqrt 2` on cuspidal
  classes; Sato--Tate makes the extremal `|a_2|` over level-`p` forms
  approach `2 sqrt 2` slowly, matching the observed slow decrease.  Two
  gaps in this argument: Eisenstein classes (Hecke eigenvalue `3`, not
  square-integrable, Steinberg- and principal-series-isotypic), and the
  comparison between the cochain Hilbert--Schmidt norm and the Petersson
  norm on harmonic representatives, which must be uniform in `d`; the
  coboundary directions are controlled by Selberg's `(tau)`.
- **What it would give.**  With uniform second-derivative bounds (the
  mismatch map is a fixed polynomial in the generators), a
  Newton--Kantorovich iteration with dimension-free constants yields
  `D(pi) <= K def(pi)` for pairs within a fixed distance of the compatible
  locus: the near sector of `iwahori-local-global-defect-question`.  It
  says nothing about pairs built from non-congruence representations of
  `SL_2(Z)`, where no Hecke structure exists; that far sector is the
  `iwahori-outlier-repair` lane.
