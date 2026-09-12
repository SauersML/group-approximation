---
rg: 2
id: atiyah-amalgam-rank-cohn-coproduct-proof
kind: route
title: Division closures nest, group rings of amalgams are coproducts, and Sylvester ranks pull back and sit below inner rank
target: atiyah-amalgam-rank-from-cohn-coproduct
requires: []
artifacts:
  - research/artifacts/atiyah-vertex-mixing-2026-09-12.md
---

The full proof is in the artifact. In outline:

1. **Nesting of division closures.** `X = D_A cap U(C)` contains `K[C]` and is division closed in
   `U(C)`. An element of `X` invertible in `U(C)` has the same inverse in `U(A)`, and `D_A` is
   division closed there. So `D_C <= X <= D_A`. The same holds for `B`.
2. **The two maps.** `phi` comes from the coproduct property of `R`. `K[G] = K[A] *_(K[C]) K[B]`
   as `K`-algebras: algebra maps agreeing on `K[C]` restrict to unit-group homomorphisms that
   agree on `C`, and these extend over the amalgam `G`. That gives `psi`. Then `phi o psi` and
   the inclusion agree on `A cup B`, so they are equal.
3. **Integrality.** `Y -> rk_G(phi(Y))` is a Sylvester matrix rank function on `R`, and
   `rk_G(M) = rk_G(phi(psi(M)))` for `M` over `K[G]`.
4. **Inner rank bound.** For `Y = PQ` through `r` columns, `rk(Y) <= rk(P) <= r`. The inner rank
   is integer valued, so equality everywhere forces integrality, and a non-integral `M` is
   strictly rank deficient after `psi`.

The inputs are standard facts about `U(G)`: the unital inclusion `U(H) <= U(G)` for `H <= G`,
and the Sylvester rank function `rk_G`. Nothing about `C` is used.
