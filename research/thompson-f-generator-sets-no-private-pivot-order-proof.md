---
rg: 2
id: thompson-f-generator-sets-no-private-pivot-order-proof
kind: route
title: Merging two roots of a forest split by a cut either crosses the cut and has one surviving peel, or stays inside a block and has at least two
target: thompson-f-generator-sets-admit-no-private-pivot-order
requires:
  - thompson-f-p22-monomials-admit-no-private-pivot-order
artifacts:
  - experiments/thompson-f-2026-09-17/xm_two_block_stubborn.py
  - experiments/thompson-f-2026-09-17/xm_two_block_stubborn.out
  - experiments/thompson-f-2026-09-17/stubborn_core.cpp
---

Notation as in the claim. The required claim is used only for item 1 there: a stubborn set
kills every private pivot order.

**Coincidences for degree-one sets.** Let `w ∈ M` and `j >= 0`.
- `w = x_j z'` for some `z' ∈ M` iff root `j` of `w` is a nontrivial tree.
- In that case `z'` is `w` with the top caret of root `j` deleted, the *peel* of `w` at `j`. It is
  unique by left cancellation.
- Peels at different roots are different forests, because they have different carets.

So for `S = X_m`, `N(w)` is the set of peels of `w` at the nontrivial roots with index `<= m`.

**Setup.** Fix `m`, `D`, `N = D + m + 2` and `c` as in the theorem, and let `Z = Z(m, D, c)`.
- A forest with `D` carets, all on leaves in `[0, N)`, has exactly `N − D = m + 2` roots meeting
  `[0, N)`. Their indices are `0, ..., m+1`. The roots of index `>= m + 2` are the trivial leaves `>= N`.
- For `z ∈ Z`, no caret crosses the cut. So the first `r` roots cover `[0, c)` exactly and the
  remaining `m + 2 − r` roots cover `[c, N)`.
- Since `1 <= c < N`, we have `1 <= r <= m + 1`, so `r − 1` lies in `{0, ..., m}`.

**Nonempty.** Take `r = 1` with one tree on the `c` leaves of `[0, c)`. On `[c, N)` take any forest of
`m + 1` trees; this needs `N − c >= m + 1`, which holds because `c <= D + 1`. The two parts together
have `(c − 1) + (N − c − m − 1) = D` carets.

**Each `z ∈ Z` has exactly one `Z`-private successor.** Let `z ∈ Z`, `j <= m` and `w = x_j z`.
- *Where `w` lives.* The new caret joins roots `j` and `j + 1 <= m + 1`, which both meet `[0, N)`.
  So `w` has `D + 1` carets on `[0, N)` and `m + 1` roots meeting `[0, N)`, with indices `0..m`.
  Hence `N(w)` is the set of peels of `w` at its nontrivial roots among the roots meeting `[0, N)`.

- *Case `j = r − 1` (crossing product).* Root `r − 1` covers the last leaves before `c` and root `r`
  covers the first leaves from `c`. So the caret they form contains leaves `c − 1` and `c`.
  - Peeling `w` at any other root keeps this crossing caret, so that peel is not in `Z`.
  - Peeling at `r − 1` gives `z`.
  - So `N(w) ∩ Z = {z}`, and `w` is `Z`-private for `z`.

- *Case `j ≠ r − 1` (non-crossing product).* Roots `j` and `j + 1` lie on the same side of the cut, so
  `w` has no caret containing both `c − 1` and `c`.
  - Deleting a caret keeps every caret on `[0, N)` and creates no crossing caret. So every peel of `w`
    lies in `Z`, and `N(w) ∩ Z` is the set of peels at all nontrivial roots of `w`.
  - Suppose `N(w) ∩ Z = {z}`. Then exactly one root of `w` is nontrivial, and the other `m` roots
    meeting `[0, N)` are single leaves. So that tree has `N − m = D + 2` leaves.
  - That tree has no crossing caret, so all its leaves lie on one side of the cut. But each side has at
    most `D + 1` leaves, a contradiction.
  - So `|N(w) ∩ Z| >= 2`, and `w` is not `Z`-private for `z`.

So every `z` has exactly one `Z`-private successor, `x_(r−1) z`. Hence `Z` is stubborn, and by item 1 of
the required claim no total order on `M` gives every element two private points in `X_m m`. Such a cut
exists iff `2(D + 1) >= N`, that is `D >= m`.

**Size at `D = m`.** Here `N = 2m + 2`, and the constraints force `c = m + 1`. A member of `Z` is an
ordered forest on the leaves `[0, m+1)` with `a` carets, followed by an ordered forest on `[m+1, 2m+2)`
with `m − a` carets. The number of ordered forests of `r` binary trees with `n` leaves in total is the
ballot number `(r/n) C(2n − r − 1, n − 1)`. With `n = m + 1` and `r = n − a` this gives the formula in the
claim.

**Identification with the computed core.** `Z(m, m, m+1)` is stubborn and contained in `M_(m, 2m)`, so
it lies in `core(M_(m, 2m))`, the largest stubborn subset (union closure and peeling, from the route
of the required claim). The formula gives 2, 8, 40, 221, 1288, 7752 for `m = 1..6`. These are the core
sizes that `stubborn_core.cpp` reports. Equal sizes plus containment give equality, for `m <= 6`.

**Machine check** (`xm_two_block_stubborn.py`, output `xm_two_block_stubborn.out`). This is not needed
for the proof.
- It builds `Z(m, D, c)` from normal forms. It converts each form to a forest and multiplies by merging
  roots, independently of the insertion rule in `stubborn_core.cpp`.
- For every admissible `(m, D, c)` with `m <= 5` and `m <= D <= m + 2`, it asserts that every point has
  exactly one private successor, and that this successor is `x_(r−1) z`.
- For `m <= 6` it asserts that `Z(m, m, m+1)` equals, as a set of normal forms, the core written out by
  `stubborn_core m 2m "0;1;...;m"`.
