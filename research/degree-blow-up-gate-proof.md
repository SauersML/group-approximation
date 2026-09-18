---
rg: 2
id: degree-blow-up-gate-proof
kind: route
title: Prove the degree blow-up identities and compose the blow-up with gate (K1)
target: degree-blow-up-extends-spectral-gap-gate-to-irregular-hosts
requires: [spectral-gap-ratio-reductions-cannot-prove-ugc]
artifacts:
  - experiments/ug-blowup-regularization-2026-09-18/check_blowup.py
---

Notation is that of the target. Write `p(u_i) = u` for the copy map and
`d_u = deg(u) = m_u`. Weights of `B = B(U)` are taken before rescaling; a common
positive rescaling multiplies the adjacency and degree matrices by one scalar
and so changes neither values nor the normalized Laplacian.

## Item 1: loop-free and regular

`U` is loop-free, so every constraint `e = (u, v, π_e)` has `u != v`, and every
blown-up constraint `(u_i, v_j, π_e)` joins copies of distinct vertices. So `B`
is loop-free. The weighted degree of `u_i` is

```text
sum_(e ∋ u) sum_(j <= m_v) w_e/(m_u m_v) = sum_(e ∋ u) w_e / m_u = d_u / m_u = 1.
```

## Item 2: equal optima

*(>=)* For a labelling `Λ` of `U` put `Λ~(u_i) = Λ(u)`. A blown-up constraint
of `e` is satisfied iff `e` is, and the blown-up constraints of `e` carry total
weight `m_u m_v · w_e/(m_u m_v) = w_e`. The total weight of `B` is therefore
`W`, and `val_B(Λ~) = val_U(Λ)`.

*(<=)* Let `Λ~` label `B`. Choose indices `i_u in [m_u]` independently and
uniformly, one per vertex `u`, and put `Λ(u) = Λ~(u_(i_u))`. For a constraint
`e = (u, v, π_e)`, `u != v`, the pair `(i_u, i_v)` is uniform on
`[m_u] x [m_v]`. So

```text
Pr[Λ satisfies e] = (1/(m_u m_v)) sum_(i,j) 1[Λ~ satisfies (u_i, v_j, π_e)].
```

Multiplying by `w_e / W` and summing over `e` gives `E val_U(Λ) = val_B(Λ~)`.
Some choice attains at least the mean, so `opt(U) >= val_B(Λ~)`. This is the
only place loop-freeness of `U` is used beyond item 1: a loop would pair
`u_(i_u)` with itself.

## Item 3: spectrum

Let `P = D^(−1) A` be the walk of `U` and `P~` that of `B`. By item 1, `P~` is
the weighted adjacency of `B` itself, and its entries are

```text
P~(u_i, v_j) = w_uv / (m_u m_v) = P(u, v) / m_v,       w_uv := sum of w_e over e between u, v,
```

using `P(u, v) = w_uv / d_u = w_uv / m_u`. Split functions on the copies as
`F = f∘p + g`, where `f(u)` is the mean of `F` over the copies of `u` and `g`
has zero sum on every copy class. Then

```text
(P~ (f∘p))(u_i) = sum_v sum_j P(u,v) f(v)/m_v = (P f)(u),
(P~ g)(u_i)     = sum_v (P(u,v)/m_v) sum_j g(v_j) = 0.
```

`B` is regular, so `P~` is symmetric and the two subspaces are orthogonal for
the uniform measure. The first is invariant and `P~` acts on it as `P`; the
second, of dimension `sum_u (m_u − 1)`, is its kernel. `P` is similar to
`D^(−1/2) A D^(−1/2)` and `P~` to its own normalized adjacency, so the
normalized-Laplacian spectrum of `B` is `spec(I − P)` together with `1` of
multiplicity `sum_u (m_u − 1)`. The eigenvalue `0` occurs in the first part,
so `λ_2(B)` is the least of `λ_2(U)` and (when the second part is non-empty)
`1`.

## Item 4: size

`sum_u m_u = sum_u d_u = 2W`, and the constraint list has one entry per
`(e, i, j)`, at most `sum_e m_u m_v <= W · W^2` entries (at most `W` distinct constraints, each `m <= W`).

## Theorem 2

Let `f` be as stated and `f' = B∘f`. It is computed in polynomial time by
item 4, since `W(f(x)) <= poly(|x|)`. Its outputs are loop-free and regular
(item 1).

* If `x in L`, then by items 2 and 3,
  `λ_2(f'(x)) >= min(λ_2(f(x)), 1) >= X(s)(1 − opt(f(x))) = X(s)(1 − opt(f'(x)))`,
  and `λ_2(f'(x)) > 0` because both `λ_2(f(x))` and `1` are positive.
* If `x notin L`, then `opt(f'(x)) = opt(f(x)) <= s`.

These are exactly the hypotheses of gate (K1) of
`spectral-gap-ratio-reductions-cannot-prove-ugc` for the reduction `f'`. So
`L in P`.

## Corollary 3

For bipartite `U` with sides `A, B`, conjugating `D^(−1/2) A D^(−1/2)` by the
diagonal sign `+1` on `A`, `−1` on `B` negates it, so the normalized adjacency
spectrum is symmetric about `0` and the Laplacian spectrum about `1`. If `U` is
connected with `n >= 3` vertices, `0` is simple, so `2` is simple, and some
eigenvalue `μ` lies in `(0, 2)`. Both `μ` and `2 − μ` lie in `(0, 2)`, so
`λ_2 <= min(μ, 2 − μ) <= 1`.

## Check

`experiments/ug-blowup-regularization-2026-09-18/check_blowup.py` verifies
items 1–3 on 40 random instances (see the target).
