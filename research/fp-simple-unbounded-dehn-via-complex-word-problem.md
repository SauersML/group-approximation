---
rg: 2
id: fp-simple-unbounded-dehn-via-complex-word-problem
kind: route
title: Finitely presented simple groups beyond every recursive time bound have Dehn functions beyond every recursive bound
target: fp-simple-dehn-functions-have-no-recursive-upper-bound
requires:
  - fp-simple-groups-with-arbitrarily-complex-word-problem
  - dehn-function-bound-gives-word-problem-time-bound
---

Fix a recursive `f`.

1. **Majorize.** Fix a Turing machine computing `f` with running time `tau(m)` on
   input `m`, and put `f'(n) = n + sum_(m <= n) (f(m) + tau(m))`. It is recursive,
   non-decreasing, at least `max(f(n), n)`, and computable by running the machine on
   `0, ..., n` in time at most `C_0 f'(n)^2`.
2. **A hard simple group.** Put `T(n) = 2^(n (f'(n) + n)^2)`, which is recursive.
   `fp-simple-groups-with-arbitrarily-complex-word-problem` gives a finitely
   presented simple `S` whose word problem has no algorithm running in time
   `C T(Cl) + Cl + C` for any `C`.
3. **Transfer.** Suppose `delta_S ≼ f`. Then `delta_S ≼ f'`, and
   `dehn-function-bound-gives-word-problem-time-bound` gives an algorithm within
   `2^(C'(f'(C'l) + l)^2) + C'`. For `l >= 1` and `C'' = C'`, we have
   `C'(f'(C'l) + l)^2 <= C''l (f'(C''l) + C''l)^2`, so the algorithm runs within
   `T(C''l) + C''`. That contradicts step 2.

So `delta_S ⋠ f`. `∎`

This route gives only the weak reading of Zaremsky Problem 1.16. The premise is the
Boone–Higman region's open complexity root, which is implied by
`boone-higman-conjecture`. So a uniform recursive upper bound on Dehn functions of
finitely presented simple groups would refute that conjecture.
