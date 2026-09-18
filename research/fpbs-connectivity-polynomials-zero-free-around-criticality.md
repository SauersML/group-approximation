---
rg: 2
id: fpbs-connectivity-polynomials-zero-free-around-criticality
kind: claim
title: Every nonamenable Cayley graph has zero-free, exponentially bounded connection polynomials on a domain around p_c
distinct_from:
  fpbs-pivotal-budget-universal: that is a real-variable pivotal bound on [p_c,p_0]; this is a complex zero-free region with growth control that may avoid p_c, and it forces a flat rate, which the budget does not
  fpbs-integrated-sensitivity-universal: that locates integrated sensitivity in real parameter; this is an analytic continuation statement about the finite connection polynomials
artifacts:
  - research/artifacts/fpbs-zero-free-connectivity-2026-09-17.md
  - experiments/fpbs-zero-free-2026-09-17/tree_walk_connectivity_zeros.py
---

OPEN research hypothesis (ZG). Every nonamenable Cayley graph `G` has a simply
connected domain `U` in `C`, open intervals `I_-` in `(0,p_c]` and `I_+` in
`(p_c,1)` contained in `U`, and constants `M`, `n_0`, such that for all
`n>=n_0` and `R>=n` the walk-averaged connection polynomial `a_(n,R)(z)` has
no zero in `U` (Z) and satisfies `|a_(n,R)| <= exp(M n)` on `U` (G).

With `fpbs-zero-free-connectivity-gives-flat-rate` it gives
`fpbs-benjamini-schramm-universal`.

Status of evidence (Sections 3 and 4 of the artifact):

- On `T_d`, (G) holds with `M=0` on `|z|<=1`. (Z) on a disc about `p_c` is
  supported numerically only: for `T_3` and `n<=200`, `a_n` has no zero in
  `|z-1/2|<0.25`.
- Necessary consequences: a flat rate `lambda=rho` just past `p_c` (N1); fixed-n
  analytic continuation of `a_n` around `p_c` (N2); growth control uniform
  in `R` (N3). The parallel-routes toy `1-(1-z^L)^(2^L)` stays in `[0,1]` on
  the real axis but grows without bound off it, with zeros entering a fixed
  disc about `1/2` at `L=16`. So (G) needs cancellation among overlapping
  routes.
- First killing test: exact `a_(n,R)(z)` for small `n` and growing `R` on a
  small nonamenable Cayley graph with overlapping cycles.
