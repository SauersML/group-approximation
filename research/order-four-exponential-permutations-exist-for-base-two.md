---
rg: 2
id: order-four-exponential-permutations-exist-for-base-two
kind: claim
title: For all large odd n there are order-four permutations of Z/nZ that double x+1 against x almost everywhere
distinct_from:
  bs1m-higman-sofic-quotients-iff-exponential-permutations: that imports the equivalence for every base m; this is the existence statement for base two, the one case its source leaves open.
  higman-group-is-sofic: that asks for soficity of Higman's group, which implies this; this is equivalent only to some nontrivial sofic quotient of Higman's group.
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
  - experiments/higman-exponential-permutations-2026-09-17/sat_min_breakpoints.py
  - experiments/higman-exponential-permutations-2026-09-17/sat_order4.jsonl
  - experiments/higman-exponential-permutations-2026-09-17/sat_order4.log
  - experiments/higman-exponential-permutations-2026-09-17/sat_order3.jsonl
  - experiments/higman-exponential-permutations-2026-09-17/sat_order2.jsonl
  - experiments/higman-exponential-permutations-2026-09-17/sat_base3_order4.jsonl
  - experiments/higman-exponential-permutations-2026-09-17/two_break_exponentials.c
  - experiments/higman-exponential-permutations-2026-09-17/two_break_p400.txt
  - experiments/higman-exponential-permutations-2026-09-17/anneal_breakpoints.c
  - experiments/higman-exponential-permutations-2026-09-17/run_anneal.sh
  - experiments/higman-exponential-permutations-2026-09-17/anneal_results.txt
  - experiments/higman-exponential-permutations-2026-09-17/sat_relaxed_return.py
  - experiments/higman-exponential-permutations-2026-09-17/sat_relaxed_return.jsonl
---

**OPEN.** For every `eps > 0` there is `C` such that for every odd `n > C` there
is a bijection `f : Z/nZ -> Z/nZ` with `f^4 = id` and `f(x+1) = 2 f(x)` for at
least `(1 - eps) n` values of `x`.

**Equivalent form.** By `base-two-exponential-permutations-iff-sofic-higman-quotient`,
this holds exactly when Higman's group `H4` has a nontrivial sofic quotient.

## Attempts

1. **Random-model heuristic (Helfgott--Juschenko §`sec:heur`, l.1655–1745).**
   *Not a proof, and untrustworthy.* A random `f` with the local doubling
   property has `f^4 = id` with probability too small for any `f` to be expected
   when `eps < 1/4`. Two results defeat the analogous heuristic:
   Kassabov--Kuperberg--Riley Theorem `heuristicapplication` (base `m` with
   `ln ln n < m < ln n`), and Theorem `GS version` (every `m > 2`).
2. **`p`-adic bound (Helfgott--Juschenko Proposition `prop:norvi`, l.326–337).**
   *Too weak.* For `n = p^r` with `p ∤ m - 1`: either `f^4 != id` on at least
   `p^r / 2` points, or `f(x+1) != m f(x)` on at least `p^(r/4-1) / 2^(1/4)`
   points. A contradiction would need a positive proportion.
3. **Glebsky's `p`-quotient mechanism.** *Void for base two.* It needs a prime
   `p | m - 1`.
   `nontrivial-higman-quotients-keep-all-four-bs-subgroups` shows that no
   nontrivial quotient of `H4` has a generator of finite order, so no torsion
   quotient can play that role.
4. **Residually solvable variations (Kassabov--Kuperberg--Riley Theorem
   `ressolvable`).** *Void for base two.* It needs a homomorphism
   `G -> A x B` that `BS(1,m)` does not have (their l.503).
   `nontrivial-higman-quotients-are-not-locally-elementary-amenable` excludes
   every locally elementary amenable witness.
5. **Small-`n` search.** *Not run: it cannot certify anything.* Even for `m > 2`,
   where the permutations exist, Kassabov--Kuperberg--Riley (l.1284) believe the
   threshold is `C = O(2^(K eps^-2))`. A finite search at feasible `n` separates
   neither case.
6. **Exact small-`n` minimum, calibrated (SAT, 2026-09-17).** *Dead end, with a
   precise rule-out.* `sat_min_breakpoints.py` computes the exact minimum `S_K(n)` of
   `#{x : f(x+1) != m f(x)}` over `f` with `f^K = id`, re-verifying every model.
   - Base 2, `K = 4`, odd `n = 3..33`: `2,2,3,3,2,4,5,4,4,6,5,5,6,6,7,6`.
     Also `S_4(35) >= 6`. The optimum at `n = 11` is the pure exponential
     `f(1) = 0`, `f(x) = 7 * 2^(x-2)`.
   - Base 3, `K = 4`, the case Kassabov--Kuperberg--Riley prove true,
     `n = 5,7,11,13,17,19,23,25,29`: `2,2,3,5,4,4,5,6,6`.
   - Base 2, `K = 3`, where the cover is trivial and `S_3(n) >= kappa n`,
     odd `n = 3..25`: `2,2,3,3,2,4,5,5,5,6,6,7`.
   - Base 2, `K = 2`, odd `n = 3..25`: `2,2,3,3,4,5,6,6,8,9,9,10`.

   *What it rules out.* Only `C(eps) >= n` whenever `eps < S_4(n)/n`, for instance
   `C(eps) >= 31` for `eps < 7/31`. The true base-3 case, the open base-2 case and
   the provably linear `K = 3` case are indistinguishable at `n <= 33`
   (`|S_4(n) - S_3(n)| <= 2` for all odd `n <= 25`), so exact search at feasible `n`
   gives no evidence either way. This confirms Attempt 5 by measurement.
7. **Two-breakpoint exponentials (exhaustive).** *Dead end.* A permutation with
   exactly two breakpoints is `f(s-1) = 0`, `f(s+k) = g 2^k`, with `p` prime and 2
   primitive. `two_break_exponentials.c` checks all `p(p-1)` candidates for
   `f^4 = id`: solutions exist only for `p = 3, 5, 11` among such primes `p <= 400`.
   So "discrete exponential plus one seam" is not a family. Any sublinear family
   needs a growing number of seams.
8. **Simulated annealing on order-`K` conjugacy classes.** *Dead end for
   detecting `o(n)`.* `anneal_breakpoints.c` moves inside a fixed cycle type by
   transposition conjugation, so `f^K = id` holds exactly throughout.
   `run_anneal.sh` reproduces `anneal_results.txt`. The best ratios found in one
   run with `min(20000 n, 6e7)` steps, for `K = 2/3/4`:
   - `n = 101`: `.485/.426/.376`
   - `n = 301`: `.535/.455/.415`
   - `n = 1001`: `.562/.475/.472`
   - `n = 3001`: `.581/.513/.513`

   The ratio grows with `n`. At `n = 1001` and `n = 3001` the `K = 3` case (trivial
   group) and the `K = 4` case agree to within `0.01`.
   The landscape is glassy: local search does not find the exponential structure
   that already beats it at `n = 11`. This rules out unstructured local search as a
   certificate source in either direction.
9. **Subsequence and relaxed return suffice.**
   `one-matcher-sequence-gives-sofic-higman-quotient` shows the statement is
   equivalent to `liminf S'(n)/n = 0`. There `S'` also counts `f^4(2x) != 2 f^4(x)`
   in place of requiring `f^4 = id`. So a search may target one sequence of moduli
   and any `f` whose fourth power almost commutes with doubling. The dichotomy is
   sharp: either `S(n) = o(n)` along all odd `n`, or `S'(n) >= kappa n` for all
   odd `n >= 3`.

   *Measured.* `sat_relaxed_return.py` computes `S'(n)` exactly for odd
   `n = 3..29`. It equals `S_4(n)` at every such `n`, and some minimizer has
   `f^4 = id`. The relaxation enlarges the certificate class but does not lower the
   small-`n` minima.
