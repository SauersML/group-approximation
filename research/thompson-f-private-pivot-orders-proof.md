---
rg: 2
id: thompson-f-private-pivot-orders-proof
kind: route
title: Private points are disjoint across factors, and the order-minimal factor of a support isolates two coordinates with an invertible minor
target: thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs
requires:
  - thompson-f-nonamenable-iff-some-monomial-set-doubles
artifacts:
  - research/artifacts/hl-f-p22-invariant-2026-09-13.md
---

Notation as in the claim.

**Finiteness of factor sets.** Left multiplication by `x_p` inserts one letter into a normal form and
leaves the other letters unchanged. This is the insertion rule used in step 2 of
`thompson-f-p22-explicit-pair-degree-bound-wiedemann-proof`, and it is checked against the rewriting
system by `experiments/thompson-f/p22inv/pivot_orders.py`. Hence left division by `x_p` is unique when it
exists, and `w ∈ S m` for at most `|S|` elements `m`. So `m_<(w)` is well defined.

**Item 1.** Each `w` is private for exactly one `m`, namely `m_<(w)`. For finite `Y`, the private points of
the `m ∈ Y` are pairwise disjoint subsets of `S Y`, each of size at least 2. So `|S Y| ≥ 2|Y|`, i.e. `S` is
doubling. Item 1 of `thompson-f-nonamenable-iff-some-monomial-set-doubles` says that if `F` is amenable,
no finite subset of `M` is doubling. So `F` is not amenable.

**Item 2.** Let `u, v ∈ K[M]` with `a u = b v`, and suppose `Y = supp u ∪ supp v` is nonempty. Let `m*` be
the `<`-minimum of `Y`, with chosen private points `w_i = s_i m*` (`i = 1, 2`).
- *Which terms reach `w_i`.* The coefficient of `a u − b v` at `w_i` is `Σ (α_s u(m) − β_s v(m))`, summed
  over all `(s, m)` with `s m = w_i`.
  - Every such `m` satisfies `m ≤ m_<(w_i) = m*`.
  - Elements `m < m*` are not in `Y`, because `m*` is minimal.
  - For `m = m*`, left cancellation in `F` leaves only `s = s_i`.
- *The two coordinates.* So `(a u − b v)(w_i) = α_(s_i) u(m*) − β_(s_i) v(m*)`. Both vanish, and the
  minor `α_(s_1) β_(s_2) − α_(s_2) β_(s_1)` is nonzero, so `u(m*) = v(m*) = 0`.
- *Contradiction.* That contradicts `m* ∈ Y`. Hence `u = v = 0`.

**Item 3.** `pivot_orders.py` does two things.
1. It checks the insertion and left-division formulas against the rewriting `x_j x_i -> x_i x_(j+1)`
   (`i < j`) on 20000 random instances.
2. For seven orders on normal forms, it computes the private points of every `m` of degree `<= 4` with
   letters `<= 7`. The private counts don't depend on the letter bound, because factors of `w` only
   delete letters of `w`.

The first `m` with fewer than two private points:
- `lex`, `revlex`, `sum_lex`, `sum_revlex`: `m = x_0`, 1 private point;
- `colex_neg`, `lex_neg`, `sum_neg_lex`: `m = x_4`, 1 private point.

By hand for `lex` at `m = x_0`: `x_0 x_1 · x_0 = x_0 x_0 x_2` also equals `x_0 x_0 · x_2`, and `x_2 > x_0`.
So that point is not private for `x_0`. The output file is md5 `47c8f2678adf58406fef57a5ca245133`.
