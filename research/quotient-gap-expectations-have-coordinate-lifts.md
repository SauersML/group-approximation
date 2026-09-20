---
rg: 2
id: quotient-gap-expectations-have-coordinate-lifts
kind: claim
title: "A quotient spectral gap gives a coordinate lift of the full commutant expectation"
distinct_from:
  kazhdan-commutants-are-internal: "This supplies a coordinate linear map for the expectation; it does not supply finite subalgebras representing its range."
artifacts:
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Proposition 3.1. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

Fix a nonprincipal ultrafilter omega, dimensions d_n, a fixed finite list of unitaries u_(j,n), and their images u_j in M = prod_omega M_(d_n). Put C = {u_j}' cap M and let T_n be the lazy symmetric conjugation average, so E_n(x) = <(I-T_n)x,x> = (4h)^(-1) sum_j ||[u_(j,n),x]||_2^2. Suppose T has spectral gap a>0 on L^2(C)^perp.

There are integers ell_n ->_omega infinity such that Phi_n = T_n^(ell_n) induces E_C on EVERY operator-norm-bounded sequence. For every sequence of unital finite subalgebras A_n in M_(d_n),
```
[A_n]_omega = C iff ||Phi_n - E_(A_n)||_(infinity->2) ->_omega 0.
```
More generally the criterion holds for any uniformly operator- and 2-norm-bounded coordinate maps inducing E_C. This is not internality: existence of A_n is a separate question.

Source: Liu, Proposition 3.1. The bounded-sequence witness argument and diagonalization are written in the proof route. For a Kazhdan representation the conjugation representation gives the required quotient gap.
