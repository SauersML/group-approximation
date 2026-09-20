---
rg: 2
id: dln-galois-symmetry-of-modular-twists
kind: claim
title: In a modular category the Galois group acts on simple labels by a signed permutation of the S-matrix, and twist ratios transform by the square of the Galois automorphism
---

**ESTABLISHED by citation** (`dln-galois-symmetry-of-modular-twists-citation`). Unreviewed.

Let `A` be a modular category over `C`: a braided spherical fusion category with invertible S-matrix
`s~_ij = ptr(c_(V_j,V_i*) c_(V_i*,V_j))`. Let `Pi` be its set of simple labels, `0` the unit, and
`theta_i` the twist scalars. Let `s = rho(s)` for a modular representation `rho` of `A`. By (4.1) of the
source, `s` is a nonzero scalar multiple of `s~`, so homogeneous relations such as `s_ij = s_ik` hold for
`s` iff they hold for `s~`.

1. **(DLN0) Finite order.** The twist has finite order, so every `theta_i` is a root of unity.
2. **(DLN1) Signed permutation.** For every `sigma in Aut(Q_ab)` there are a permutation `sigma^` of
   `Pi` and a sign function `eps_sigma : Pi -> {+-1}` such that
   ```text
   sigma(s_ij) = eps_sigma(i) s_(sigma^(i), j)   for all i, j in Pi.
   ```
3. **(DLN2) Squared Galois action on twists.** For every `sigma in Aut(Q_ab)` and `i in Pi`,
   ```text
   theta_(sigma^(i))  =  theta_(sigma^(0)) * sigma^2(theta_i).
   ```
   In particular, for all `i, j in Pi`,
   ```text
   theta_(sigma^(i)) / theta_(sigma^(j))  =  sigma^2( theta_i / theta_j ).
   ```

Item 1 is the finite-order statement of Section 1.3 of the source. Item 2 is its (4.3). Item 3 is its
Proposition 4.7, (4.12). The last display divides two instances of (4.12), and the factor
`theta_(sigma^(0))` cancels.
