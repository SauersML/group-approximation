---
rg: 2
id: pure-braid-top-bnsr-invariants-are-center-nonvanishing
kind: claim
title: "For m >= n-2, Sigma^m(P_n) consists exactly of the characters that do not vanish on the full twist"
distinct_from:
  zaremsky-1-09-bnsr-invariants-of-pure-braid-groups: that claim is the whole question for every m; this settles only the range m >= n-2.
  pure-braid-bns-invariant-is-circle-complement: that claim computes Sigma^1 only; this computes Sigma^m for m >= n-2, which for n = 3 is Sigma^1 again (the equator of P_3 = F_2 x Z).
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-top-range-2026-09-13.md
---

For every `n >= 3` and every `m >= n - 2` (including `m = infinity`),

    Sigma^m(P_n) = { [chi] : chi(Delta^2) != 0 } = { [sum a_{ij} omega_{ij}] : sum_{i<j} a_{ij} != 0 },

so the complement of `Sigma^m(P_n)` in `S(P_n)` is the great subsphere
`{sum_{i<j} a_{ij} = 0}` of dimension `binom(n,2) - 2`. For `H_n = P_n / Z(P_n)`
(the pure mapping class group of the `(n+1)`-punctured sphere),
`Sigma^m(H_n)` is empty for `m >= n - 2`.

Consequences:

- `Sigma^2(P_4) = Sigma^infinity(P_4)` is the complement of the great 4-sphere
  `{a12 + a13 + a14 + a23 + a24 + a34 = 0}`. Zaremsky (arXiv:1507.08597v1, p. 2)
  recorded this computation as open. With Koban–McCammond–Meier, all BNSR
  invariants of `P_n` are now computed for `n <= 4`.
- A coabelian subgroup `N <= P_n` is of type `F_{n-2}` (equivalently
  `F_infinity`) iff `P_n/N` has torsion-free rank at most 1 and, when that rank
  is 1, `Delta^2` has infinite order in `P_n/N` (via Bieri–Geoghegan–Kochloukova,
  Theorem 1.1).

Status: UNREVIEWED (lane z1-09-pure-braid, 2026-09-13). Novelty check bounded;
artifact Section 8.
