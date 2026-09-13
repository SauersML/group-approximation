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
