---
rg: 2
id: fpbs-replica-meet-cap-inf-fails-free-products-proof
kind: route
title: Bridges swapped by t give infinitely many infinite clusters below 1, and the meet of the unique infinite plane clusters is an infinite invariant set inside the replica meet
target: fpbs-replica-meet-cap-inf-fails-free-products
requires:
  - fpbs-cluster-count-trichotomy
  - fpbs-hp-relative-burton-keane
  - fpbs-replica-meet-threshold-sandwich
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-cap-inf-counterexample-2026-09-19.md
  - experiments/replica-meet-free-product-2026-09-17/peierls_bound.py
---

Complete proof in Section 2 of the artifact.

0. **Structure.**
   - By the normal form for free products, contracting the planes `gA` gives
     the Bass–Serre tree, so every `t`-edge is a bridge.
   - An element `a` of order at least 3 exists in `A`, because exponent-2
     groups are abelian. Then `<a, tat>` contains a nonabelian free group, so
     `A * Z/2` is nonamenable.
1. **`p_u = 1`.**
   - Take the bridge `e = {o,t}` and let `alpha = P(o ↔ ∞ inside W_o)`.
     Left multiplication by `t` swaps the two sides of `e`, and
     `theta <= 2 alpha`.
   - By independence over disjoint edge sets,
     `P(N >= 2) >= alpha^2 (1-p) > 0` for `p in (p_c, 1)`.
   - The trichotomy in `fpbs-cluster-count-trichotomy` then gives `N = ∞`.
     If `p_u < 1`, simultaneous uniqueness would contradict this.
2. **`p_cap^(k) <= p_c(L)`.**
   - For `p > p_c(L)`, each replica restricted to the plane `L` through `o`
     has exactly one infinite cluster `C_i`. This is
     `fpbs-hp-relative-burton-keane` with `H = A` on `L`.
   - `D = C_1 ∩ ... ∩ C_k` has an `A`-invariant law and
     `P(o in D) = theta_L(p)^k > 0`.
   - By Lemma 1.1 of the sandwich proof, restated in the artifact,
     `P(o in D, |D| < ∞) = 0`.
   - `D ⊆ M_k(o)` on `{o in D}`. Monotonicity in `p` finishes.
3. **Instance.** The Peierls bound gives `p_c(Z^2) <= 9/10`. The script checks
   it with exact rationals: `837/12250 < 1`.
