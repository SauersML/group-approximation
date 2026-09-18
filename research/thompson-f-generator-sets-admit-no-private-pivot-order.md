---
rg: 2
id: thompson-f-generator-sets-admit-no-private-pivot-order
kind: claim
title: For every m, the set of forests on D + m + 2 leaves with no caret across one cut is stubborn for X_m = {x_0..x_m}, so no generator set X_m has a private pivot order
distinct_from:
  thompson-f-p22-monomials-admit-no-private-pivot-order: that defines stubborn sets and finds one by computer for S_(3,5), and records the X_m cores for m <= 6 as computed data; this proves by hand an explicit stubborn set for every X_m and every D >= m, and identifies it with the computed core at D = m.
  thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs: that turns a pivot order into doubling and non-Ore pairs; this shows the hypothesis never holds for S = X_m, for any m.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that is the doubling criterion; this kills only the order-based certificate for doubling of X_m, not doubling itself.
artifacts:
  - experiments/thompson-f-2026-09-17/xm_two_block_stubborn.py
  - experiments/thompson-f-2026-09-17/xm_two_block_stubborn.out
  - experiments/thompson-f-2026-09-17/degree_one_stubborn_census.py
  - experiments/thompson-f-2026-09-17/degree_one_stubborn_census.jsonl
  - experiments/thompson-f-2026-09-17/stubborn_core.cpp
  - experiments/thompson-f-2026-09-17/stubborn_census.jsonl
---

**ESTABLISHED** through `thompson-f-generator-sets-no-private-pivot-order-proof` (direct proof, with
computer checks of the finite cases; not independently reviewed; no priority claimed).

Notation as in `thompson-f-p22-monomials-admit-no-private-pivot-order`.
- `M` is the positive monoid of `F`, viewed as forests of binary trees on the leaves `0, 1, 2, ...`,
  with finitely many carets. `M_D` is the set of forests with `D` carets.
- `x_j z` adds one caret joining roots `j` and `j+1` of `z`.
- For a degree-one set `S`, `N(w) = {z : w ∈ S z}`.
- A finite nonempty `Z ⊆ M_D` is *stubborn for `S`* if every `z ∈ Z` has at most one `w ∈ S z` with
  `N(w) ∩ Z = {z}`. If a stubborn set exists, no total order on `M` gives every element two private
  points (item 1 there). So no private pivot order exists for `S`.

Let `X_m = {x_0, ..., x_m}`.

**Theorem (two-block stubborn sets).** Let `m >= 1` and `D >= m`, and put `N = D + m + 2`. Choose a cut
`c` with `1 <= c < N`, `c <= D + 1` and `N − c <= D + 1`. Let `Z(m, D, c) ⊆ M_D` be the set of forests
with `D` carets such that:
- every caret lies on leaves in `[0, N)`;
- no caret has both leaf `c − 1` and leaf `c` below it.

Then `Z(m, D, c)` is nonempty and stubborn for `X_m`. More precisely, every `z ∈ Z(m, D, c)` has
**exactly one** `Z`-private successor, namely the crossing product `x_(r − 1) z`, where `r` is the
number of roots of `z` whose leaves lie in `[0, c)`.

**Corollaries.**
1. **No generator set `X_m` has a private pivot order**, for any `m >= 1`. For `m <= 2` this already
   follows from item 3 of `thompson-f-p22-monomials-admit-no-private-pivot-order`, because the census
   table there records layers with `Λ_(X_m) < 2`. For `m >= 3` that table records no such layer, so the
   corollary is new there. The order-based (triangular) certificate can never show that any `X_m`
   doubles.
2. **The computed cores are these sets.** At `D = m` the only admissible cut is `c = m + 1` (two blocks
   of `m + 1` leaves). Then
   `|Z(m, m, m+1)| = Σ_(a=0..m) f(m+1, a) f(m+1, m−a)`, where `f(n, a) = (r/n) C(2n − r − 1, n − 1)` with
   `r = n − a` is the number of ordered forests of `r` binary trees with `n` leaves in total.
   - The values for `m = 1..6` are 2, 8, 40, 221, 1288, 7752.
   - These equal the census sizes of `core(M_(m,2m))` in `stubborn_census.jsonl`.
   - `xm_two_block_stubborn.py` checks that the sets coincide for `m <= 6`.
   - So the census row "`X_m`: first core at `D = m`" is proved for the existence half. The
     emptiness below `D = m` is still computed only, inside `M_(D, m + D)`.
3. **Where every order dies.** Under any total order, the minimum `z` of `Z(m, D, c)` has only the
   crossing product as a possible private point. Each non-crossing product `x_j z` is shared with another
   member of `Z`, obtained by peeling a different root.

**Data (degree-one census, computed, not proved;** `degree_one_stubborn_census.jsonl`**).** For every
`J ⊆ {0..5}` with `|J| = q >= 2`, the least `D <= 8` with `core(M_(D, max J + D + 1)) ≠ ∅` for
`S = {x_j : j ∈ J}` is `D = q − 1`.
- Most `J` give the same core size as `X_(q−1)`: 2, 8, 40, 221, 1288.
- The exceptions are `q = 4` with 52 for `{0,1,3,4}`, `{0,1,3,5}`, `{0,2,4,5}`, `{1,2,4,5}` and 36 for
  `{0,1,4,5}`, and `q = 5` with 320 for `{0,1,2,4,5}` and `{0,1,3,4,5}`.
- **Conjecture:** every finite degree-one set `S` of size `q >= 2` has a stubborn set in `M_(q−1)`.

**Scope.**
- This decides neither `thompson-f-is-amenable` nor doubling of any `X_m`. It kills one certificate
  class for one family of generating sets.
- **Why the block construction does not transfer:**
  - *Gapped `J`.* Block sets fail for `J = {0,1,4}`: an exhaustive search over `N <= 11`, `D <= 5` and
    up to three blocks finds none, although a core exists at `D = 2`. This search is not archived and
    should be treated as a remark.
  - *Degree 2 and higher.* For `S` of degree `k >= 2` (for example `S_(2,4) = X_1 X_2`, with a
    24-point core at `D = 4`), a crossing product can own several points. The computed cores are not
    block sets: the `X_1 X_2` core contains crossing trees.
- **Open:** whether the flagship `S_(3,5)` stubborn set (1092 points, `D = 7`) has a structural
  description, and whether `{x_a x_b x_c : a <= 2, b <= 3, c <= 4}` has any stubborn set (none through
  `D = 10`).
