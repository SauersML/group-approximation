---
rg: 2
id: sofically-dominated-integral-matrices-obey-determinant
kind: claim
title: Over every group, an integral self-adjoint matrix that dominates an injective integral element of a sofic subrelation has Fuglede--Kadison determinant at least 1
distinct_from:
  diagonally-dominant-integral-matrices-obey-determinant: that is one operator class, proved through Lyons' tree-entropy bound; this is a criterion for all self-adjoint integral matrices, which reproves the infinite part of that class through a treeable subrelation and also covers operators that are not diagonally dominant, such as Cayley Laplacians minus a constant
  determinant-conjecture-holds-for-sofic-groups: that needs the whole group to be sofic; this needs only some injective integral operator below the matrix to live on a sofic subgroup or a sofic subrelation of an orbit relation, over a group that may be nonsofic
  measure-theoretic-determinant-conjecture: that is the open bound for every relation; this uses only its proved sofic case (Elek--Lippner) and transfers it upward by operator monotonicity
---

**ESTABLISHED** by `sofically-dominated-determinant-proof`. Not independently
reviewed. It combines standard facts (Fuglede--Kadison monotonicity and
Elek--Lippner's sofic case of the measurable determinant conjecture); the
content is the criterion and what it kills.

## Statement

Let `G` be a countable group and `T in M_n(Z[G])` self-adjoint. Suppose there
are:
- an essentially free probability-measure-preserving action of `G` on
  `(X, mu)`, with orbit relation `R`, and its amplification `R^(n)` on
  `X x [n]` (`(x,i) ~ (y,j)` iff `x R y`);
- a **sofic** subrelation `R'` of `R^(n)`;
- a self-adjoint `S in ZR'` with `0 <= S <= T` in `N(R^(n))` and `ker S = 0`.

Then `T` is injective and `det_N(G)(T) >= det_N(R')(S) >= 1`.

**Subgroup form.** If `H <= G` is sofic and `S in M_n(Z[H])` is injective with
`0 <= S <= T`, then `det_N(G)(T) >= 1`.

## Corollaries

- **(Diagonally dominant, second proof.)** The infinite part of
  `diagonally-dominant-integral-matrices-obey-determinant` follows
  with `R'` the treeable relation "same tree of the wired uniform spanning
  forest" and `S = S_F`. This replaces Lyons' `h >= 0` by Elek--Lippner and
  needs no gauge.
- **(Laplacian minus a constant.)** Let `s_1, ..., s_k in G` be a multiset,
  `Delta = sum_i (1 - s_i)^*(1 - s_i)`, and split the indices as `A ⊔ B`. Let
  `c >= 0` be at most the bottom of the spectrum of `Delta_A` on
  `l^2(<s_i : i in A>)`. If `<s_i : i in B>` is sofic and infinite, then
  `Delta - c` obeys the determinant conjecture.
  - **Example.** `G` any group containing a free subgroup `<a,b,c>` of rank 3
    and an element `g` of infinite order (`g = a` is allowed):
    `T = Delta_(a,b,c,g) - 1`. Kesten gives `lambda_0(Delta_(a,b,c)) = 6 - 2 sqrt 5 > 1`.
  - `T` is not diagonally dominant (diagonal `7`, off-diagonal mass `8`), has
    infinite spectrum and norm above two. So none of the earlier necessary
    shapes on `determinant-conjecture-counterexample-exists` excludes it.

## What it rules out

- **A violation dominates nothing sofic.** If `T` violates the conjecture, then
  for every free action, every sofic subrelation `R'` of `R^(n)` (treeable,
  hyperfinite, or the orbit relation of a sofic subgroup) and every
  integer-valued `S in ZR'`, `0 <= S <= T` forces `ker S != 0`.
- **Laplacian-minus-constant candidates must be tight.** For `Delta_X - c` to
  violate, removing any infinite sofic sub-multiset of generators (for example
  one element of infinite order) must push the bottom of the spectrum of the
  rest below `c`.
- **Open inside this family.** Whether a random sofic `S` can certify
  `Delta_X - c` when no deterministic split of the generators works is not
  settled here. A forest term `S_F` would need `Delta_(X \ F) >= c` at every
  realization.

## Limit of the method

- **Row restriction never helps a square matrix.** Let `B in M_n(Z[G])` and
  `T = B^*B`. For a Borel set `H` of rows and `P_H` its projection in
  `N(R^(n))`, `S_H = B^* P_H B <= T`. If `S_H` is injective, then `P_H B` is
  injective, so its range projection has trace `n`, which is at most
  `tr(P_H) <= n`. Hence `P_H = 1`. So the square cubic operators
  `1 + w_1 + w_2` to which lane sw-046 reduces the injective case cannot be
  handled by keeping a sofic random set of rows; a dominated `S` must mix
  rows.
