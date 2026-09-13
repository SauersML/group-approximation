---
rg: 2
id: pure-braided-bht-braid-characters-dimension-n-n-minus-1
kind: claim
title: "The pure braid kernel of bF_{n,r} carries an n(n-1)-dimensional space of invariant characters, so Hom(bF_{n,r}, R) has rank n^2"
---

Let `n >= 2`, `r >= 1`, `d = n - 1`, and `bF_{n,r} = N ⋊ F_{n,r}` with `N` the
directed union of pure braid groups on the leaves of forests. Then
`Hom(bF_{n,r}, R) = pi^* Hom(F_{n,r}, R) ⊕ W` with `W = Hom(N, R)^{F_{n,r}}`, and:

1. A leaf pair `i < j` of a forest with `k` leaves has a *type*: whether
   `i = 1`, whether `j = i + 1`, whether `j = k`, and the residues `i - 1`,
   `j - i - 1` mod `d`. Two pairs lie in one `F_{n,r}`-orbit iff their types
   agree (a PL map with slopes in `<n>` preserves lengths mod `d Z[1/n]`).
2. `W` is the space of functions on types that are additive under `n`-fold
   splitting of either leaf. It has dimension `n(n - 1)`: free data are a
   `(Z/d)^2`-array on interior non-adjacent pairs with zero row and antidiagonal
   sums (`(d-1)^2`), zero-sum functions on pairs from the first leaf and on
   pairs to the last leaf (`d - 1` each), any function on interior adjacent
   pairs (`d`), and the value on the first–last pair (`1`).
3. With `Hom(F_{n,r}, R)` of rank `n`, `Hom(bF_{n,r}, R)` has rank `n^2`.
4. The value `tau_phi(k)` of `phi` in `W` on the full twist of all `k` strands
   of any forest depends only on `k` and is affine in `k` on `k >= 3`,
   `k ≡ r mod d`. The map `phi -> tau_phi` onto affine functions is onto, so
   the full-twist-invisible subspace `W_0` has dimension `n(n-1) - 2`: zero for
   `n = 2`, positive for `n >= 3`.

For `n = 2` this recovers the basis `omega_0`, `omega_1` of Zaremsky
(arXiv:1403.8132 Lemma 1.7, `F_br^{ab} = Z^4`). For `n = 3` a new character is
`A_{ij} -> (-1)^{j-i-1}` on non-adjacent interior leaves (with compensating
boundary values).

Unreviewed. Proof: `research/artifacts/zp-pure-braided-bht-characters-2026-09-13.md`.
