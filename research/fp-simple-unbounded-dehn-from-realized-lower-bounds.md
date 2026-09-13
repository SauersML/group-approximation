---
rg: 2
id: fp-simple-unbounded-dehn-from-realized-lower-bounds
kind: route
title: Realized recursive lower bounds on Dehn functions of finitely presented simple groups rule out every recursive upper bound
target: fp-simple-dehn-functions-have-no-recursive-upper-bound
requires:
  - fp-simple-dehn-functions-realize-every-recursive-lower-bound
---

Fix a recursive `f`. Put `f'(n) = max_(m <= n) f(m)`, which is recursive,
non-decreasing and at least `f`, and put `g(n) = n f'(n^2) + n^2`, which is
recursive.

1. By the premise there is a finitely presented simple group `S` with
   `g ≼ delta_S`: some `K` has `g(n) <= K delta_S(Kn) + Kn`.
2. Suppose `delta_S ≼ f`, say `delta_S(m) <= K' f(K'm) + K'm`. Since `f <= f'` and
   `f'` is non-decreasing, with `K'' = K^2 K' + K` we get
   `g(n) <= K K' f'(K K' n) + K^2 K' n + K n <= K'' f'(K'' n) + K'' n`.
3. For `n > K''` we have `K'' n <= n^2` and `f'(K'' n) <= f'(n^2)`, so
   `K'' f'(K'' n) + K'' n <= K'' f'(n^2) + n^2`. If `f'(n^2) >= 1` this is `< g(n)`;
   if `f'(n^2) = 0` it is `K'' n < n^2 = g(n)`. Either way step 2 fails for every
   `n > K''`, a contradiction.

So `delta_S ⋠ f`. `∎`
