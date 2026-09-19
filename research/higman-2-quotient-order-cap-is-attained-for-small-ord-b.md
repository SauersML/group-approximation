---
rg: 2
id: higman-2-quotient-order-cap-is-attained-for-small-ord-b
kind: claim
title: In the finite 2-quotients of H4(3)/<<[a,c]^2>> the cap ord(a) <= 64 ord(b) is attained exactly for ord(b) = 1 and 2 (ord(a) = 32 and 128) by explicit monolithic models of order 2^14 and 2^111, the second with ord(c) = 8; in the rotation-symmetric quotient all four orders are equal and double at classes 1, 2, 3, 4, 7, 9, 11
distinct_from:
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that asks whether H4(3)/<<[a,c]^2>> has generators of infinite order in its 2-quotients; this does not settle it, but shows the cap ord(a) <= 64 ord(b) is sharp for ord(b) <= 2 and reduces unboundedness to sharpness of the cap along the family G/<<b^(2^k)>>.
  higman-j-odometer-models-restrict-to-single-cycle-models: that proves the cap and finds ord(a) = 128 in the full class-11 2-quotient (order 2^1172) and in G/<<b^4, c^8>>; this computes the exact maximum of ord(a) under b^2 = 1 and under b = 1, with small certified monolithic models, and the rotation-symmetric quotient.
  higman-torsion-generator-quotients-factor-through-tree-lattices: that shows every torsion-generator quotient factors through Gamma(3,m); the models here are finite quotients of Gamma(3,128) and Gamma(3,32) with the cap orders.
artifacts:
  - experiments/higman-pro2-order-of-a-2026-09-19/grow2.g
  - experiments/higman-pro2-order-of-a-2026-09-19/loop2.g
  - experiments/higman-pro2-order-of-a-2026-09-19/loop3.g
  - experiments/higman-pro2-order-of-a-2026-09-19/run2.sh
  - experiments/higman-pro2-order-of-a-2026-09-19/run3.sh
  - experiments/higman-pro2-order-of-a-2026-09-19/run4.sh
  - experiments/higman-pro2-order-of-a-2026-09-19/pqx.g
  - experiments/higman-pro2-order-of-a-2026-09-19/pqE.g
  - experiments/higman-pro2-order-of-a-2026-09-19/mono.g
  - experiments/higman-pro2-order-of-a-2026-09-19/check-model.g
  - experiments/higman-pro2-order-of-a-2026-09-19/permsmall.g
  - experiments/higman-pro2-order-of-a-2026-09-19/model-b1-a32-pc.g
  - experiments/higman-pro2-order-of-a-2026-09-19/model-b1-a32-perm.g
  - experiments/higman-pro2-order-of-a-2026-09-19/model-b2-a128-pc.g
  - experiments/higman-pro2-order-of-a-2026-09-19/results.txt
---

**ESTABLISHED** (proposed; items 1 and 3 proved, items 2 and 4 certified by computation, item 5
computed) by `higman-2-quotient-order-cap-is-attained-for-small-ord-b-proof`.

**Setting.** `G = H4(3)/<<[a,c]^2>>` with `H4(3) = < a,b,c,d | b^a = b^3, c^b = c^3, d^c = d^3,
a^d = a^3 >`, `x^y = y^-1 x y`. `P_cl(X)` is the class-`cl` quotient of `X` for the lower exponent-2
central series. `Gamma_k = G/<<b^(2^k)>>`, and `G'' = G/<<[b,d]^2>>`.

**Statement.**
1. **Cap.** If `x^y = x^3`, `y^(2^m) = 1` and `x` has 2-power order, then `x^(2^(m+2)) = 1`, and
   `x^2 = 1` when `m = 0`. So in every 2-quotient of `Gamma_k` with `k >= 1`: `ord(c) | 2^(k+2)`,
   `ord(d) | 2^(k+4)`, `ord(a) | 2^(k+6)`; for `k = 0`: `ord(c) | 2`, `ord(d) | 8`, `ord(a) | 32`.
2. **The cap is attained for k = 0, 1.**
   - `Gamma_0` has a monolithic 2-quotient of order `2^14` with orders `(a,b,c,d) = (32,1,2,8)`, and a
     faithful transitive model on 256 points.
   - `Gamma_1` has a monolithic 2-quotient `M_1` of order `2^111` with orders `(128,2,8,32)`: all four
     orders sit at their caps, and `ord(c) = 8`.
   - So the largest order of `a` in a finite 2-quotient is exactly 32 under `b = 1` and exactly 128
     under `b^2 = 1`. Both models are saved as pc presentations and checked by `check-model.g`.
3. **Symmetric quotient.** The rotation `a -> b -> c -> d -> a` is an automorphism of `G''`. So in every
   `P_cl(G'')` the four generators have the same order, and `ord(a)` in `P_cl(G)` is at least that.
4. **Doubling classes.** In `P_cl(G'')` the common order is `2,4,8,16,16,16,32,32,64,64,128,128,128` for
   `cl = 1..13` (orders `2^4 ... 2^1526`), so it doubles at classes 1, 2, 3, 4, 7, 9, 11, the classes found
   for `ord(a)` in `P_cl(G)`. In `P_cl(Gamma_1)`, `ord(a)` doubles at 1, 2, 3, 4, 7, 9, 12, and it has
   reached the cap 128 at class 12.
5. **Toward k = 2.** In `P_cl(G''/<<b^4>>)`, `ord(a)` is `2,4,8,16,16,16,32,32,64,64,64,128,128` for
   `cl = 1..13`, doubling at 1, 2, 3, 4, 7, 9, 12 as in `Gamma_1`. `P_13` has order `2^1184` and orders
   `(128,4,16,64)`: `b, c, d` are at their caps and `a` is one doubling short of its cap 256.

**Reduction.** If the cap is attained for every `k >= 1` (a 2-quotient of `Gamma_k` with
`ord(a) = 2^(k+6)`), then `ord(a)` is unbounded in the 2-quotients of `G` and `a` has infinite order in
the pro-2 completion. This is now verified for `k = 1` (and the `k = 0` cap 32 is attained too).

**Dead.** Truncating each new central layer to a random subspace of fixed dimension (always keeping the
power tails of the generators) loses later doublings. With 4, 8 or 16 kept dimensions `ord(a)`
stops at 32, 32, 64 by class 14, against 128 in the full quotient. Growth of `ord(a)` needs the whole
layer, not the generator tails alone.

**Next.** Push `P_cl(G''/<<b^4>>)` past class 13 (class 14 is running from the saved workspace) to decide whether `ord(a) = 256` (the `k = 2` cap). Then
look for the lift `Gamma_k -> Gamma_(k+1)` in the monolithic models: `M_1` has `c` of order 8 acting on
`<d> = C_32`, which is exactly the input a self-similar step would need.
