---
rg: 2
id: zaremsky-2-13-bnsr-of-pure-braided-bht-groups
kind: claim
title: "Zaremsky Problem 2.13 resolved: compute the BNSR invariants of the pure braided Brown–Higman–Thompson groups bF_{n,r}"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 13,
verbatim: "Compute the BNSR-invariants of the pure braided
Brown–Higman–Thompson groups bF_{n,r}."

This claim is the question. It is established only through an answer route:

- **Computation**: `zaremsky-2-13-by-computation` requires an answer claim that
  describes `Sigma^m(bF_{n,r})` explicitly for every `m >= 1`, `n >= 2`,
  `r >= 1`. The current candidate answer is
  `pure-braided-bht-sigma-invariants-miss-only-endpoint-hull`.

Never write a `requires: []` route into this claim.

## Precise reading

- `bF_{n,r}` (`n >= 2`, `r >= 1`): elements are classes of triples
  `(T_-, b, T_+)` where `T_-`, `T_+` are `n`-ary forests with `r` roots and the
  same number `k` of leaves, and `b` is a pure braid on `k` strands; expansion
  of a leaf cables its strand into `n` parallel strands. Forgetting `b` gives
  a split surjection `bF_{n,r} -> F_{n,r}` (the section is `b = 1`) whose kernel
  is the directed union `PB_infinity` of the pure braid groups attached to
  forests. `bF_{2,1}` is the pure braided Thompson group `F_br`.
- Finiteness: `bF_{d,r}(H)` is of type `F_n` iff the label group `H` is
  (Skipper–Wu, arXiv:2103.14589, abstract: "for all d >= 2 and r >= 1, the
  group bV_{d,r}(H) (resp. bT_{d,r}(H) or bF_{d,r}(H)) is of type F_n if and
  only if H is"); with trivial labels `bF_{n,r}` is of type `F_infinity`, so
  every `Sigma^m` is defined. The case `F_br` is due to
  Bux–Fluch–Marschler–Witzel–Zaremsky, arXiv:1210.2931.
- An answer lists a basis of `Hom(bF_{n,r}, R)` and, for each `m`, exactly
  which character classes lie in `Sigma^m`.

## Known cases

- `n = 2`, `r = 1`: Zaremsky, arXiv:1403.8132, computes
  `Sigma^1(F_br) = S^3 \ {[phi_0], [phi_1]}`; Zaremsky, arXiv:1803.02717,
  Theorem 5.1: for `m >= 2`, `Sigma^m(F_br)` is `S^3` minus the convex hull of
  `[phi_0]` and `[phi_1]`. Basis there: `phi_0`, `phi_1` (pulled back from
  `F`, depths of the first and last leaves), `omega_0` (winding number of the
  first and last strands), `omega_1` (sum of the winding numbers of
  consecutive strands). The method is a CAT(0) Stein–Farley cube complex
  (Theorem 4.6 there) with Morse theory on descending links.
- Unbraided `F_n = F_{n,infinity}` (`n >= 2`): Zaremsky, arXiv:1502.02620,
  Theorem A: `Sigma^m(F_n) = Sigma^2(F_n)` for `m >= 2`, and
  `a chi_0 + c_0 psi_0 + ... + c_{n-3} psi_{n-3} + b chi_1` fails to lie in
  `Sigma^m(F_n)` iff all `c_i = 0` and `a, b >= 0`.

## Attempts

- 2026-09-13 (lane z2-13-pure-braided-bht): computing `Hom(bF_{n,r}, R)` as
  `Hom(F_{n,r}, R)` plus the `F_{n,r}`-invariant characters of `PB_infinity`.
  The invariant characters are functions on orbit types of ordered pairs of
  leaf intervals, additive under `n`-fold splitting. For `n >= 3` the orbit
  types carry residues mod `n - 1` (a PL map with slopes in `<n>` preserves
  interval lengths mod `(n - 1)Z[1/n]`), so there are more braid characters
  than for `F_br`; the count is being checked. Then: extend the CAT(0) cube
  complex and descending-link argument of arXiv:1803.02717 to `n`-ary forests
  with `r` roots.
