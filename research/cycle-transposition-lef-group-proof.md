---
rg: 2
id: cycle-transposition-lef-group-proof
kind: route
title: Commutators of overlapping transpositions isolate one coordinate, and the torsion bound excludes every regular tree
target: cycle-transposition-lef-group-has-no-regular-tree-action
requires:
  - regular-tree-torsion-orders-have-primes-at-most-degree
---

Words act right to left. For `x in Z/n`, write `x~` for its representative in
`(-n/2, n/2]`. The *support* of an element of `Gamma` is the set of `n` where
its coordinate is nontrivial.

1. **Residual finiteness.** `Gamma` is a subgroup of a product of finite
   groups. Any element other than the identity has a nontrivial coordinate,
   and projecting to that coordinate separates it from `1`.

2. **Word problem.** Let `w` be a word of length `l` in `sigma^(+-1)` and `tau`.
   Let `e(w)` be its exponent sum in `sigma`. Let `w_inf` be the permutation of
   `Z` defined by the same word, with `sigma_inf(x) = x+1` and `tau_inf = (0 1)`.

   *Claim.* `w = 1` in `Gamma` if and only if all three hold:
   - (a) `w_n = 1` for `3 <= n <= 4l+4`;
   - (b) `e(w) = 0`;
   - (c) `w_inf` fixes every integer `x` with `|x| <= l+1`.

   Fix `n >= 4l+5` and `x in Z/n`, and follow `x` through the letters. Each
   letter moves the current point by at most one step, and `tau_n` moves only
   the residues `0` and `1`.
   - *Case `|x~| >= l+2`.* While `tau` has not acted, the integer path starting
     at `x~` has absolute value at least `|x~| - l >= 2` and at most
     `n/2 + l < n-1`. So its residue is never `0` or `1`, `tau` never acts, and
     `w_n(x) = x + e(w)`.
   - *Case `|x~| <= l+1`.* The integer path stays in `[-2l-1, 2l+1]`. There the
     residues `0` and `1` occur only at the integers `0` and `1`. So
     `w_n(x) = w_inf(x~) mod n`.

   Since `n >= 2l+5`, points of the first kind exist. Hence `w_n = 1` if and only
   if two things hold:
   - `e(w) = 0`, because `|e(w)| <= l < n`;
   - `w_inf(x~) = x~` whenever `|x~| <= l+1`, because both sides lie in
     `[-2l-1, 2l+1]`, which maps injectively to `Z/n`.

   This proves the claim, and checking (a)–(c) takes `O(l^3)` steps.

3. **Elements supported on one coordinate.** For `k in Z`, put
   `c_k = [tau, sigma^k tau sigma^-k]`.
   - In coordinate `n`, the element `sigma^k tau sigma^-k` is the transposition
     `(k, k+1)`.
   - Two transpositions commute when they are equal or disjoint. Otherwise their
     commutator is the square of a 3-cycle, which is a 3-cycle.
   - For `n >= 3`, the transpositions `(0 1)` and `(k k+1)` share exactly one
     point if and only if `k ≡ ±1 (mod n)`.

   Hence the support of `c_k` is `{ n >= 3 : n | k-1 or n | k+1 }`.

   Let `p >= 5` be prime, and put `g_p = [c_(p+1), c_(p-1)]`.
   - The supports of `c_(p+1)` and `c_(p-1)` are `{p} ∪ {n >= 3 : n | p+2}` and
     `{p} ∪ {n >= 3 : n | p-2}`. Also `p` divides neither `p+2` nor `p-2`.
   - A common element `n != p` would divide `(p+2) - (p-2) = 4` and the odd
     number `p+2`, so `n = 1`, which is excluded.
   - So `g_p` is trivial in every coordinate `n != p`.
   - In coordinate `p`, `c_(p+1)` and `c_(p-1)` are 3-cycles on `{0,1,2}` and
     `{-1,0,1}`. These supports share exactly two points (using `p >= 5`), and
     two such 3-cycles do not commute. So `g_p != 1`, and `g_p` is even, being a
     commutator.

4. **A copy of Alt(p) inside Gamma.** Let `N_p` be the normal closure of `g_p`
   in `Gamma`.
   - Conjugates and products of elements trivial off coordinate `p` stay
     trivial off `p`. So the projection `pi_p` is injective on `N_p`.
   - `pi_p(N_p)` is the normal closure of `pi_p(g_p)` in `pi_p(Gamma)`.
   - `pi_p(Gamma) = Sym(Z/p)`, because a `p`-cycle and an adjacent transposition
     generate it.
   - A nontrivial even permutation has normal closure `Alt(p)` in `Sym(p)` when
     `p >= 5`.

   So `N_p ≅ Alt(p)`. It contains a `p`-cycle, which has order `p`.

5. **No regular tree.** By
   `regular-tree-torsion-orders-have-primes-at-most-degree`, a subgroup of
   `Aut(T_d)` has no element of prime order `p > d`. Step 4 supplies such an
   element for every `d`. So `Gamma` embeds in no `Aut(T_d)`.

6. **Not residually W_d.** Composition factors of groups in `W_d` are
   composition factors of subgroups of `S_d`, so their orders are at most `d!`.
   For a prime `p > d >= 2`, we have `|Alt(p)| = p!/2 >= (d+1)!/2 > d!`. So the
   simple group `N_p` has trivial image in every quotient of `Gamma` that lies
   in `W_d`, and `N_p != 1`. `∎`

The artifact records a machine check on MSI of steps 2–4 for small cases.
