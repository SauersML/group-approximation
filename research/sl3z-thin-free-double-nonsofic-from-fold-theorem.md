---
rg: 2
id: sl3z-thin-free-double-nonsofic-from-fold-theorem
kind: route
title: Profinite density, congruence factorization and arbitrary-modulus expansion feed the amalgam fold theorem
target: sl3z-thin-free-double-nonsofic-if-sl3z-flexibly-stable
requires:
  - codense-tau-amalgams-fold-under-flexible-stability
  - explicit-sl3-thin-codense-tau-pair
  - sln-z-thin-codense-tau-pair
---

Apply the double case of `codense-tau-amalgams-fold-under-flexible-stability`
with `A = SL_3(Z)` and `C = <a,b>`. There are three hypotheses to check.

**1. `C` is dense in the profinite topology of `A`.**
- `explicit-sl3-thin-codense-tau-pair` gives `pi_m(C) = SL_3(Z/m)` for every `m`,
  which is `(ES1)`.
- It also records that every finite-dimensional unitary representation of `A`
  factors through a congruence quotient.
- Let `N` be a finite-index normal subgroup of `A`. The permutation
  representation on `l2(A/N)` has kernel `N` and factors through some
  `SL_3(Z/m)`, so `N` contains the principal congruence kernel `Gamma(m)`.
- Hence `CN >= C Gamma(m) = A`.

**2. (tau-C).** Let `X` be a finite `A`-set.
- **Reduction to a finite group.** `l2(X)` is a finite-dimensional unitary
  representation `pi` of `A`, so it factors through `Q = SL_3(Z/m)` for some
  `m`. `C` acts through `pi_m(C) = Q`, with the symmetric generating set
  `S = {a^(+-1), b^(+-1)}`.
- **Uniform expansion.** The explicit pair node imports Bourgain--Varju's
  arbitrary-modulus theorem: there is `c > 0` such that the Cayley multigraphs
  `Cay(SL_3(Z/m), pi_m S)` have edge expansion at least `c` for all `m`.
- **Spectral bound on nontrivial irreducibles.** Every nontrivial irreducible
  representation of `Q` occurs in `l2(Q)` orthogonally to the constants. For
  `eta` orthogonal to the `C`-fixed vectors, put `M = sum_{s in S} pi(s)`.
  Since `S` is symmetric, the spectrum of `M` on such `eta` lies in the spectrum
  of the adjacency operator of the 4-regular Cayley multigraph on `l2_0(Q)`.
  So `<M eta, eta> <= lambda_2 ||eta||^2`.
- **Cheeger.** The discrete Cheeger inequality for `k`-regular graphs,
  `k - lambda_2 >= h^2/(2k)`, gives `4 - lambda_2 >= c^2/8`.
- **The gap.** Therefore

  ```text
  sum_{s in S} || pi(s) eta - eta ||^2 = 2 (4 ||eta||^2 - <M eta, eta>) >= (c^2/4) ||eta||^2,
  ```

  so `max_s || pi(s) eta - eta || >= (c/4) ||eta||`, and (tau-C) holds with
  `kappa = c/4`.

**3. `C` is proper.** The order-three matrix `r` of `(ES3)` is not in the free
group `C`.

**Conclusion.** The double case of the fold theorem gives: if `A` is flexibly
stable then `D = A *_C A` is not sofic, and the fold word
`i_0(r) i_1(r)^(-1)` is nontrivial by the normal form theorem.

- **Becker--Lubotzky version.** A Becker--Lubotzky flexible solution of a
  stability challenge consists of homomorphisms on `t_k >= n_k` points, at
  vanishing flexible distance on generators. Such a solution is a Bowen--Burton
  conjugacy to a perfect approximation: closeness passes to each fixed element
  through word length, and `n_k/t_k -> 1`. So the Becker--Lubotzky hypothesis
  suffices.
- **Every `n >= 3`.** `sln-z-thin-codense-tau-pair` supplies the four-generated
  free profinitely dense subgroup, congruence factorization and the same
  expansion input. With `|S| = 8` the computation above gives `kappa = c/8`.
