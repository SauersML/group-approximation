---
rg: 2
id: excised-thick-torus-kills-width-matched-one-sided-repair-proof
kind: route
target: excised-thick-torus-kills-width-matched-one-sided-repair
title: Proof that the excised thick torus has profile at most 2k, one cylinder of height 1 in each direction, and one-sided regluing costs a and k(a-1)+1
requires:
  - near-exact-tuples-saturate-linear-conversion-defect
  - tall-cylinder-seams-reglue-within-quadratic-profile
---

**Setup.** Fix `k >= 1` and `a >= 2k + 1`, and put `W = a^2 + 1` and `n = W - k`. Let `K = {k, ..., W-1}`, a subset of
`Z/W`; the holes are `0, ..., k-1`. For `p in K` let `b_E(p)` be the first of `p+1, p+2, ...` that lies in `K`, and let
`c_E(p)` be the first of `p+a, p+2a, ...` that lies in `K`. These are the first-return maps of `b_T = +1` and
`c_T = +a` to `K`, so they are permutations of `K`. Since `gcd(a, W) = 1`, `b_T` and `c_T` are `W`-cycles, and first
returns of a single cycle to `K` are single `n`-cycles. So `b_E` and `c_E` are `n`-cycles.

**1. Distance and profile.** Extend `b_E` and `c_E` by the identity on the holes, and call the results `b'` and `c'`.
They are permutations of `Z/W`.
- `b_T(p) = b'(p)` except at `p = W-1` and at the holes. The first-return formula gives `b_T = b' pi`, where `pi` is
  the `(k+1)`-cycle `(W-1, 0, 1, ..., k-1)`. Indeed `b'(pi(W-1)) = b'(0) = 0`, `b'(pi(h)) = b'(h+1) = h+1` for
  `h < k-1`, and `b'(pi(k-1)) = b'(W-1) = k`. So `rank(b_T - b') = rank(pi - I) = k`.
- A point `p in K` has `p + a` a hole exactly when `p = h - a = W - a + h` with `0 <= h < k`. Then `p in K`, and
  `c_E(p) = h + a`, which is in `K` since `a > k`. So `c_T = c' tau`, where `tau` is the product of the `k` disjoint
  transpositions `(h - a, h)`. Indeed `c'(tau(h - a)) = c'(h) = h` and `c'(tau(h)) = c'(h - a) = h + a`. So
  `rank(c_T - c') = k`.

The pair `(b_T, c_T)` commutes. Lemma B of `near-exact-tuples-saturate-linear-conversion-defect-proof` gives
`Lambda_rect(b', c') <= 2k`, and the commutators of `(b', c')` are those of `(b_E, c_E)` plus the identity on the holes.
Hence `Lambda_rect(E) <= 2k`.

**2. Horizontal coordinates.** Label `K` by `y = p - k`, which lies in `Z/n`. Then `b_E(y) = y + 1` for every `y`
(the only skip is `W-1 -> k`, that is `n-1 -> 0`). Compute `c_E(p)` for `p in K`.
- If `p <= W - 1 - a`, that is `0 <= y <= n - a - 1`, then `c_E(y) = y + a`.
- If `W - a <= p <= W - a + k - 1`, then `p + a - W` is a hole and `c_E(p) = p + 2a - W`. In labels this is
  `c_E(y) = y + 2a - W = y + 2a - k` modulo `n`.
- If `W - a + k <= p <= W - 1`, then `c_E(p) = p + a - W`, which lies in `K`, so `c_E(y) = y + a - k` modulo `n`.

These are intervals of lengths `n - a`, `k` and `a - k`. The three translations are distinct modulo `n`, because
`0 < k < a < n`. Their breaks (points `y` with `c_E(y+1) != c_E(y) + 1`) are the three right endpoints. These are
exactly the points just before the columns that `c_E` lands next to a hole.

*Cylinders.* The only row is the `n`-cycle `b_E`, and `c_E` is not equivariant on it, since it has breaks. So the
horizontal decomposition is one cylinder `C` with `w = n` and `h = 1`, and the seam maps its top to its own bottom. By
the same argument with `c_E` in place of `b_E` (Section 4 shows that `b_E` has breaks in `c`-order), the vertical
decomposition is also one cylinder with `w = n` and `h = 1`. A single cylinder is matched to itself, so `w' = w` is
matchable and `sum_j h_j |w_j - w'_j| = 0`. There are no seams joining distinct widths, so Theorem 3 of
`tall-cylinder-seams-reglue-within-quadratic-profile` says nothing. And `tau = 1`, so `w / tau = n`.

**3. Horizontal one-sided cost.** A permutation `c''` commuting with the `n`-cycle `b_E` is a power of it, that is
`y -> y + r` in these labels. It agrees with `c_E` exactly on the interval of translation `r`, which has at most
`max(n - a, k, a - k) = n - a` points, since `n - a >= a` when `a >= 3`. So `#{c'' != c_E} >= a`, with equality for
`r = a`. □

**4. Vertical coordinates.** In `T`, label `p` by `i(p) = p a^(-1)` in `Z/W`, so that `c_T(i) = i + 1`. Since
`a^2 = -1`, `a^(-1) = -a` and `b_T(i) = i - a`. The holes have labels `i(h) = -h a`: the points
`0, W - a, ..., W - (k-1) a`, consecutive at spacing exactly `a`, and the gap from `0` forward to `W - (k-1)a` has
length `W - (k-1) a > a`. The first-return map `c_E` is `i -> i + 1` on the non-hole labels, so relabel them by
`j(i) = #(non-holes in [0, i))`, which lies in `Z/n`. Then `c_E(j) = j + 1`.

For a non-hole `p` with `p + 1` not a hole, `b_E(p) = p + 1`, which has label `i - a`. The number of non-holes in the
cyclic interval `[i - a, i)` is `a - #(holes in [i - a, i))`. So `b_E` acts as `j -> j + f`, with
`f = -a + #(holes in [i - a, i))`. By the spacing, a cyclic half-open interval of length `a` contains 0 or 1 holes.
It contains exactly 1 exactly when `i` lies in the arc `A = (W - (k-1)a, a]`, the union of the `k` intervals
`(i(h), i(h) + a]`, which has length `ka`. The arc contains the `k - 1` holes `0, W - a, ..., W - (k-2)a` (the hole
`W - (k-1) a` is its excluded endpoint). So `A` has `k(a-1) + 1` non-holes.

The only non-hole `p` whose successor is a hole is `p = W - 1`. Its label is `i = -(W-1) a = a`, which is in `A`. Its
image `k` has label `-ka`, and `[-ka, a)` contains the `k` holes and `(k+1)a - k` non-holes, so there
`f = -(k+1)a + k`. Hence, in `c`-order, `b_E` is translation by
- `-a + 1` on the `k(a - 1)` points of `A` other than `i = a`,
- `-a` on the `n - k(a-1) - 1` points outside `A`,
- `-(k+1)a + k` at the one point `i = a`.

These three values are distinct modulo `n`: the differences are `1`, `k(a-1)` and `k(a-1) + 1`, all in `(0, n)`. In
particular `b_E` has breaks in `c`-order.

**5. Vertical one-sided cost.** A permutation `b''` commuting with the `n`-cycle `c_E` is `j -> j + r`. It agrees with
`b_E` exactly on the class of translation `r`. The largest class is the one outside `A`, because
`n - k(a-1) - 1 >= k(a-1)` is equivalent to `a^2 - 2ka + k >= 0`, which holds for `a >= 2k`. So
`#{b'' != b_E} >= k(a-1) + 1`, with equality for `r = -a`. □

**6. The class killed.** Consider a repair of the form "perform column moves (pad or delete a column of a height-`h`
cylinder, cost `O(h)` in each generator) whose number is bounded by a function of `sum_j h_j |w_j - w'_j|` for a
matchable `w'`, then reglue one generator". On `E`, with the minimal `w' = w`, this performs no moves and then pays
at least `min(a, k(a-1)+1) = a` (Sections 3 and 5), while `Lambda_rect(E) <= 2k` and `d = a^2 + 1 - k`. So it has no
bound `F(K)` independent of `d`. The width data (one cylinder `(n, 1)` in each direction, self-glued) is the same for
every `k`, and it is also the data of the rotation pair `(+1, +a)` on `Z/n` with `c` perturbed on `a` points. So the
number and places of the needed column moves are not functions of the widths and heights. The repair that works is
Section 1: `k` insertions, at the holes, next to the breaks of Section 2. □

**Computation.** `experiments/doubly-wide-2026-09-18/run3.py` checks Sections 1–5 numerically for
`a in {5, 7, 9, 11, 13}` and `k in {1, 2, 3}`. It finds `rho_hat <= 2k`, one cylinder `(n, 1)` in each direction,
horizontal cost `a` and vertical cost `k(a-1)+1`. The single exception is `a = 5, k = 3` (vertical cost 11), which is
outside `a >= 2k + 1`: there the class inside `A` is the larger one, with `n - k(a-1) = 11`. Output:
`experiments/doubly-wide-2026-09-18/summary.txt`.
