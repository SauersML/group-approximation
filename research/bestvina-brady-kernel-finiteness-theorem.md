---
rg: 2
id: bestvina-brady-kernel-finiteness-theorem
kind: claim
title: The Bestvina--Brady kernel of a right-angled Artin group is of type F_n iff the flag complex is (n-1)-connected, and of type FP_n(R) iff it is (n-1)-acyclic over R
---

Let `L` be a finite flag complex and `BB_L` the kernel of the homomorphism `A_L → Z` sending every
generator to `1`. For `n ≥ 1`:

1. `BB_L` is of type `F_n` iff `L` is `(n−1)`-connected;
2. for a commutative ring `R`, `BB_L` is of type `FP_n(R)` iff `L` is `(n−1)`-acyclic over `R`.

Source: M. Bestvina and N. Brady, *Morse theory and finiteness properties of groups*, Invent.
Math. 129 (1997), 445--470, doi:10.1007/s002220050168. The printed Main Theorem is imported
verbatim as `bestvina-brady-main-theorem`; it states `FP_{n+1}(R)` ⟺ homologically `n`-connected,
`FP(R)` ⟺ acyclic, and finitely presented ⟺ simply connected. Statement (2) here is its item (1)
with the index shifted.

Derivation of (1) from the Main Theorem (route `bestvina-brady-kernel-finiteness-theorem-proof`).
- `n = 1`: type `F_1` is finite generation, which is `FP_1(Z)`; by Main Theorem (1) with index `0`
  this holds iff `L` is homologically `0`-connected, i.e. connected.
- `n ≥ 2`: a group is of type `F_n` iff it is finitely presented and of type `FP_n(Z)` (C. T. C. Wall).
  By Main Theorem (3) and (1), this holds iff `L` is simply connected and `H̃_i(L; Z) = 0` for
  `i ≤ n − 1`. By the Hurewicz theorem that is equivalent to `L` being `(n−1)`-connected.

## Attempts

- 2026-09-13, lane z1-19-raag-kernel: the Main Theorem is imported with a verified citation
  (`bestvina-brady-main-theorem-citation`). The derivation route was held back until
  z-verify-topology had reviewed `raag-finite-index-sigma-m-forces-connected-flag-complex`, so
  that Zaremsky's Problem 1.19 root would not compile as established before review. That review
  passed (`research/artifacts/zp-review-topology-2026-09-13-part3.md`, §14), and the route has
  landed.
