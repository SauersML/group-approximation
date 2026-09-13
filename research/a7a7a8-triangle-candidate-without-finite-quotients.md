---
rg: 2
id: a7a7a8-triangle-candidate-without-finite-quotients
kind: claim
title: One of the four explicit (A_7, A_7, A_8) Z/7 hyperbolic triangle groups has no nontrivial finite quotient
distinct_from:
  hyperbolic-simple-triangle-group-without-finite-quotients: that asks for some member of the whole simple-vertex class; this asks it of four explicit members
---

Let `G_1, …, G_4` be the four triangles of groups recorded in
`research/artifacts/simple-vertex-triangle-quotient-search-2026-09-12.md` §2:
- vertex groups `A_7, A_7, A_8`, given by generating pairs of 7-elements;
- edge groups `Z/7` with the twists `e`;
- trivial face group;
- links of girth `6, 6, 8`.

Claim: at least one `G_i` has no nontrivial finite quotient.

**OPEN.**

## Attempts

- **Permutation and small Lie-type quotients (2026-09-13).** A complete, calibrated
  double-coset search finds no nontrivial homomorphism `G_i -> S_n` for `n <= 30`. It also finds
  none into `Sp_6(2)`, `L_5(2)`, `L_6(2)`, `O_8^+(2)`, `O_8^-(2)` or `L_4(4)`. See
  `research/artifacts/hyperbolic-triangle-quotient-search-2026-09-13.md`. Degrees up to 14 are
  forced by support, so from degree 15 on this is evidence only.
- **4-dimensional representations in characteristic 2 are ruled out**
  (`a7a7a8-triangle-candidates-no-4dim-char2-representation`, computer-assisted). This is the
  smallest dimension of a faithful representation of `A_8` over any field. For `G_2` and `G_4` an
  eigenvalue sign obstruction already kills it; for `G_1` and `G_3` a trace-ideal Gröbner basis is `(1)`.
- **Where it dies.** Every search above is finite. A decision would need to exclude every
  finite simple group. The same large-quotient barrier stops
  `hyperbolic-simple-triangle-group-without-finite-quotients`.
- **Calibration warning.** Caprace–Conder–Kaluba–Witzel `G^{14,14,18}_4` survived all small
  quotient searches and then had `PSp_6(p)` quotients from a 6-dimensional representation. The
  next tests are therefore the representations in dimensions 6 (characteristic 2) and 7
  (characteristic 0 and odd characteristic).
