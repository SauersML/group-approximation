---
rg: 2
id: infinite-simple-group-permutation-stable-iff-nonsofic-proof
kind: route
title: The limit kernel of an almost action is normal, so simplicity makes it trivial or everything, and amplification turns trivial into soficity
target: infinite-simple-group-permutation-stable-iff-nonsofic
requires: []
artifacts:
  - research/artifacts/un-stability-nonsofic-2026-09-13-part1.md
---

Notation: `d = d_H`, normalized Hamming distance on `Sym(k)`. It is bi-invariant, so
`d(ab, cb) = d(a, c)` and `d(xax^-1, 1) = d(a, 1)`. Soficity means: for every finite `F ⊆ S` and
`epsilon > 0` there is `phi : S -> Sym(k)` with `d(phi(gh), phi(g)phi(h)) < epsilon` for `g, h ∈ F`,
and `d(phi(g), 1) > 1 - epsilon` for `g ∈ F \ {1}`.

**(2) ⇒ (3).** Take `rho_n` trivial; then `d(phi_n(g), rho_n(g)) = d(phi_n(g), 1) -> 0`.

**(3) ⇒ (4).** Take `k'_n = k_n`.

**(4) ⇒ (2).** Every homomorphism `rho : S -> Sym(k')` is trivial. Its kernel is normal, so it is
`1` or `S`; it is not `1`, because an infinite group does not embed in a finite one. So the
restriction of `rho_n(g)` to `[k_n]` is the identity, and the flexible distance on `[k_n]` is
exactly `d(phi_n(g), 1)`, which therefore tends to `0`.

**(2) ⇒ (1).** If `S` were sofic, diagonalizing over an exhaustion of `S` by finite sets gives an
almost homomorphism with `d(phi_n(g), 1) -> 1` for each `g != 1`. Such a `g` exists because `S` is
infinite, contradicting 2.

**(1) ⇒ (2).** Suppose 2 fails for some almost homomorphism `phi_n` and some `g_0`. Pass to a
subsequence with `d(phi_n(g_0), 1) >= c > 0`, and fix a nonprincipal ultrafilter `omega` on it. Put
`N = {g : lim_omega d(phi_n(g), 1) = 0}`.
- `phi_n(1)` is asymptotically trivial: `d(phi_n(1), 1) = d(phi_n(1)phi_n(1), phi_n(1)) ≤ d(phi_n(1·1), phi_n(1)phi_n(1)) -> 0`.
- **N is a subgroup.**
  - Products: `d(phi(gh), 1) ≤ d(phi(gh), phi(g)phi(h)) + d(phi(g), 1) + d(phi(h), 1)`.
  - Inverses: `d(phi(g^-1), 1) ≤ d(phi(g)phi(g^-1), 1) + d(phi(g), 1)`, and `d(phi(g)phi(g^-1), 1)`
    is at most the defect at `(g, g^-1)` plus `d(phi(1), 1)`.
- **N is normal.** `d(phi(hgh^-1), 1) ≤ d(phi(h)phi(g)phi(h)^-1, 1) + o(1) = d(phi(g), 1) + o(1)`.
  The `o(1)` term is a sum of finitely many defects.
- **N is trivial.** `g_0 ∉ N`, so `N != S`, and `N = 1` by simplicity. Hence
  `c_g := lim_omega d(phi_n(g), 1) > 0` for every `g != 1`.

**Amplification.** For `m >= 1`, let `phi_n^(m) : S -> Sym(k_n^m)` act coordinatewise.
- A point is fixed iff every coordinate is fixed, so `1 - d(phi^(m)(g), 1) = (1 - d(phi(g), 1))^m`.
- By a union bound over coordinates, `d(phi^(m)(gh), phi^(m)(g)phi^(m)(h)) ≤ m · d(phi(gh), phi(g)phi(h))`.

Given finite `F` and `epsilon > 0`:
- choose `m` with `(1 - c/2)^m < epsilon`, where `c = min_{g ∈ F \ {1}} c_g > 0`;
- then choose `n` in the `omega`-large set where `d(phi_n(g), 1) >= c_g/2` for `g ∈ F \ {1}` and
  every defect on `F × F` is below `epsilon/m`.

Then `phi_n^(m)` is `epsilon`-multiplicative and `epsilon`-free on `F`, so `S` is sofic,
contradicting 1. QED

**Model tests.**
- `S = A_5` (finite simple) fails the hypothesis "infinite": it has faithful genuine actions and is sofic and stable. The proof of (4) ⇒ (2) correctly uses infiniteness.
- Not simple, e.g. `S = Z`: the kernel `N` can be a proper nontrivial subgroup, and the step `N = 1` needs simplicity. Indeed `Z` is sofic and stable.
