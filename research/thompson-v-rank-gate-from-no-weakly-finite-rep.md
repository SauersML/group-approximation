---
rg: 2
id: thompson-v-rank-gate-from-no-weakly-finite-rep
kind: route
title: Rank ultraproducts are weakly finite, so no weakly finite characteristic-two representation of V means no rank model
target: thompson-v-has-no-nontrivial-f2-rank-model
requires:
  - thompson-v-has-no-weakly-finite-char-two-representation
  - sylvester-rank-function-quotients-are-weakly-finite
artifacts:
  - research/artifacts/thompson-v-weakly-finite-representations-2026-09-16.md
---

Artifact Corollary 3.3.

1. Let `B = Π_k M_(n_k)(F)` with `char F = 2`, and let `ω` be a nonprincipal ultrafilter.
2. `N(X) = lim_ω rk(X_k) / n_k`, on square matrices `X` over `B`, is a Sylvester matrix rank function with
   `N(1) = 1`.
3. Its null ideal is `N_rk`, so the rank ultraproduct `M = B / N_rk` is weakly finite by
   `sylvester-rank-function-quotients-are-weakly-finite`. It has characteristic two.
4. By the first requirement, every homomorphism `V -> M^x` is trivial.

The converse is not known. A nontrivial weakly finite characteristic-two representation of `V` need not
carry a Sylvester rank function that separates the image of `V` from `1`.
