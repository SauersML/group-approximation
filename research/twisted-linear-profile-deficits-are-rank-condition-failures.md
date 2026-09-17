---
rg: 2
id: twisted-linear-profile-deficits-are-rank-condition-failures
kind: claim
title: Twisted linear entropy profiles over a field crossed product have a Rokhlin deficit exactly when the crossed product fails the rank condition
distinct_from:
  rokhlin-window-transport-is-dominated: that proves domination for equivariant affine codes by evaluating the decoder on constant inputs; this treats invariant entropy profiles whose codeword coefficients vary with the site through a field action and cocycle, where constant inputs are unavailable, and identifies their deficits with a ring-theoretic failure.
  bernoulli-rokhlin-deficit-has-a-finitary-witness: that computes Rokhlin entropy of Bernoulli shifts as an infimum of Phi over finite configurations; this evaluates the same functional on translation-invariant, finitely entropic profiles and computes its infimum over the linear ones.
  rank-condition-rings-have-weakly-finite-images: that characterizes the rank condition by weakly finite images for any ring; this ties the rank condition of the rings K*G to entropy deficits over G.
artifacts:
  - research/artifacts/twisted-linear-entropy-profiles-2026-09-17.md
  - experiments/twisted-linear-entropy-profiles-2026-09-17/check_twisted_profile.py
---

Let `G` be a countable group and `R = K*G` a crossed product over a commutative field `K`, with any action `σ` and
2-cocycle `α`. Skew group rings, twisted group algebras and group algebras are special cases.

**Profiles.** For `v_1..v_s` in `R^k`:
- let `X_h` be the family `(u_h e_i)_i`, and `Y_h` the family `(u_h v_j)_j`;
- let `h(S) = dim_K span_K(S)`.

This `h` is translation invariant. Each finite restriction is exactly entropic after reduction to a finite field.
The site blocks are independent and uniform, and each codeword is a function of its window. The code itself is
not equivariant: its coefficients `σ_h(a) α(h,e)` vary with `h`.

**Theorem.**
1. Some twisted linear profile over `R` has `I(X_1;Y_F) > h(Y_1)` iff `R` fails the rank condition (some
   epimorphism `R^r -> R^d` with `r < d`).
2. The infimum of `Phi = (1/k)[h(Y_1) + h(X_1|Y_F)]` over these profiles is `1` if `R` has the rank condition,
   and `0` otherwise.
3. **Gate.** Suppose domination `I(x(1);y_F) <= H(y_1)` at `G` is derived only from:
   - entropy inequalities on finitely many variables;
   - independence and uniformity of sites;
   - window dependence of codewords;
   - translation invariance of the entropy function.

   Then every crossed product `K*G` over a field has the rank condition. Contrapositive: a single `K*G` without
   it defeats every such argument at `G`. It supplies an invariant, finitely entropic profile with `Phi`
   arbitrarily close to `0`.
4. **The class is not empty.** For amenable `G` the Følner chain-rule count is such an argument (artifact
   Proposition 0.3).

The gate constrains the argument, not the conclusion. A proof of maximal Bernoulli entropy on a group whose
crossed products fail the rank condition must use equivariance of the code, as constant-input and microstate
arguments do.

**ESTABLISHED 2026-09-17** by [[twisted-linear-profile-dictionary-proof]].
