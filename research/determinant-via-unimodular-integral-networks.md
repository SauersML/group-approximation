---
rg: 2
id: determinant-via-unimodular-integral-networks
kind: route
title: Realize every integral group-ring operator as a unimodular integer-weighted network and apply the Serre inequality for expected root measures
target: determinant-conjecture
requires:
  - serre-class-from-unimodular-integral-realizability
  - determinant-conjecture-iff-serre-class-spectra
---

Let `G` be any group, `n >= 1` and `A in M_n(Z[G])` self-adjoint.

1. **The network.** On the vertex set `G x {1..n}`, put integer weights
   `w((g,i),(h,j)) = A_ij(g^-1 h)`. These are symmetric because `A` is
   self-adjoint. The weighted degree is at most `sum_(i,j,g) |A_ij(g)|`.
2. **Unimodularity.** Left translation by `G` preserves the weights and is
   transitive on each fibre `G x {i}`. Rooting at `(e,i)` with `i` uniform
   gives a unimodular random rooted network: mass transport holds because
   `G` acts by automorphisms transitively on fibres and the fibre label is
   chosen uniformly.
3. **The measure.** The adjacency operator is `A` acting on `l^2(G)^n`, and the
   expected root spectral measure is
   `(1/n) sum_i <E_A(.) delta_(e,i), delta_(e,i)> = mu_A / n`.
4. **Polynomial images.** For nonzero `Q in Z[x]`, `Q(A) in M_n(Z[G])` is again
   of this form, so `serre-class-from-unimodular-integral-realizability`
   gives `integral_(Q != 0) log|Q| d mu_A >= 0`.
5. **Conclusion.** By `determinant-conjecture-iff-serre-class-spectra`,
   `det_N(G)(B) >= 1` for every `B in M_(m x n)(Z[G])`.

This route is open because its first premise is open. The premise is strictly
stronger than the determinant conjecture: it includes nonsofic unimodular
networks that are not Cayley networks.
