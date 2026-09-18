---
rg: 2
id: akkstv-degree-blowup-proof
kind: route
title: Regularize by blowing each vertex up into copies joined completely, read the spectrum off a factorization of the walk, and recover labelings by a derandomized random-copy choice
target: akkstv-rounding-holds-on-all-loop-free-constraint-graphs
requires: [unique-games-on-expanding-constraint-graphs-are-easy, spectral-gap-ratio-reductions-cannot-prove-ugc, orientation-lifts-sandwich-2to1-game-values]
artifacts:
  - experiments/ugc-akkstv-regularize-2026-09-17/check_degree_blowup.py
---

Notation is that of the target. Write `H = B_m(U)`, `N = sum_u m_u`, `n = |V(U)|`,
and `W` for the total weight. The walk matrix of a weighted graph is
`P(u,v) = w_uv/d_u`. It is self-adjoint for `<f,g>_d = sum_u d_u f_u g_u`, and
the normalized Laplacian `I − D^(−1/2) A D^(−1/2)` is similar to `I − P`.

## (1) Degrees and total weight

A copy `(u,i)` meets, for each constraint `(u,v)` of weight `w`, the `m_v` copies
of `v`, each with weight `w/(m_u m_v)`. So its degree is
`sum_v w_uv/m_u = d_u/m_u`, which is item 3. Summing over copy pairs,
`sum_(i,j) w/(m_u m_v) = w`. So every constraint of `U` keeps its total weight
and `W(H) = W(U)`. Item 4 is immediate: a loop of `H` would need `u = v`.

## (2) Spectrum

Define `Lift : R^V → R^(V(H))` by `(Lift f)(u,i) = f(u)`, and
`Avg : R^(V(H)) → R^V` by `(Avg g)(v) = (1/m_v) sum_j g(v,j)`. Then
`Avg Lift = I_n`. By (1),

```text
P_H((u,i),(v,j)) = (w_uv/(m_u m_v)) / (d_u/m_u) = P_U(u,v)/m_v,
so  (P_H g)(u,i) = sum_v P_U(u,v) (Avg g)(v),  i.e.  P_H = Lift P_U Avg.
```

For `X = Lift` (`N x n`) and `Y = P_U Avg` (`n x N`), the identity
`det(t I_N − XY) = t^(N−n) det(t I_n − YX)` gives

```text
det(t I_N − P_H) = t^(N−n) det(t I_n − P_U Avg Lift) = t^(N−n) det(t I_n − P_U).
```

So the eigenvalues of `P_H`, with multiplicity, are those of `P_U` together with
`0` repeated `N − n` times. Both walks are self-adjoint for their degree inner
products, so these are real spectra of diagonalizable operators. Passing to
`I − P` gives item 2: the Laplacian spectrum of `H` is that of `U` together with
`1` repeated `N − n` times. The smallest eigenvalue is `0`, from `U`. If
`N > n`, the second smallest is `min(λ_2(U), 1)`.

## (3) Value

*`opt(H) >= opt(U)`.* Label every copy of `u` by `x_u`. Each copy pair of a
constraint is satisfied iff the constraint is. By (1), the value is unchanged.

*`opt(U) >= opt(H)`, constructively.* Let `y` label `H`. Draw independent
uniform `i_u < m_u` and put `x_u = y(u, i_u)`. `U` is loop-free, so on each
constraint `(u,v,π)` the pair `(i_u, i_v)` is uniform on `[m_u] x [m_v]`. Then

```text
E val_U(x) = (1/W) sum_(u,v,π) w sum_(i,j) (1/(m_u m_v)) 1[π(y(u,i)) = y(v,j)] = val_H(y).
```

Fix the `i_u` one at a time, each time choosing the value that maximizes the
conditional expectation. That conditional expectation is a sum over constraints
of averages over the still-free indices, so it is computable in polynomial time.
The result is a deterministic `x` with `val_U(x) >= val_H(y)`. This is item 1,
and it also recovers labelings.

*Where loop-freeness is used.* On a loop `(u,u,π)`, the random-copy labeling
evaluates only the diagonal pairs `i = j`. `H` averages over all pairs, so the
identity fails. Loops are the one case left open.

## (4) Integer multiplicities

*Biregular bipartite.* Take `m = d_A/g` on `A` and `d_B/g` on `B`. Then
`w/(m_a m_b) = g^2/(d_A d_B)` is the same for every copy pair. Rescaling all
weights by `d_A d_B/g^2` gives multiplicity `1` per copy pair, and every copy has
degree `d_u/m_u · d_A d_B/g^2 = d_A d_B/g`. The size is
`|A| d_A/g + |B| d_B/g <= 2|E|` vertices.

*General unary input.* Let `D = lcm` and `h = gcd` of the degrees. Take
`m_u = d_u/h`. Give each copy pair of a constraint of weight `w` the integer
multiplicity `w (D/d_u)(D/d_v)`, which is `D^2 h^2/(d_u d_v)` times
`w/(m_u m_v)`. This is a constant rescaling of `B_m(U)` up to the factor
`h^2`, which cancels. Every copy then has degree `D^2/h`, and the total
multiplicity is `W (D/h)^2`. That is polynomial whenever `D/h` is, for example
when the degrees take `O(1)` distinct values.

*Arbitrary input.* Use the rational weights `w/(d_u d_v)` (`m = d`, degree `1`),
written in binary. **Reading used here:** the AKKSTV import applies to
constraint multisets whose multiplicities are written in binary. The value
`val` and the characterization (7) are expectations over the multiset, so they
are unchanged by the encoding. The rounding enumerates `nk` choices and
evaluates each labeling. The only step whose cost depends on the multiplicities
is solving the Figure 1 SDP, whose objective has them as coefficients. It is
solved to additive accuracy `γ` in time polynomial in the bit length and
`log(1/γ)`, and the quoted error `O(tη/λ + 2^(−t/2))` absorbs `γ <= η` into `η`.
The biregular and bounded-`D/h` cases above need no such reading.

## (5) Proof of (A)

Given `U`, compute `H = B_m(U)` with `m` proportional to `d`, as in (4). `H` is
loop-free and weighted-regular. By (2) `λ_2(H) = min(λ_2(U), 1) = λ`, and by (3)
`opt(H) = opt(U) >= 1 − η`. The import in the form of
`unique-games-on-expanding-constraint-graphs-are-easy` applies to `H`
(weighted-regular, `λ >= e η`). It returns `y` with
`val_H(y) >= 1 − C_A (η/λ) log(λ/η)`. The derandomized copy choice of (3) turns
`y` into a labeling of `U` of at least that value.

The degenerate case `N = n` means `m = 1` everywhere, so `U` is already regular,
and then `λ = λ_2(U)` directly.

For a bipartite `U`, the spectrum of `D^(−1/2) A D^(−1/2)` is symmetric about
`0`. So `λ_2 = 1 − σ_2 <= 1`, and `min(λ_2, 1) = λ_2`.

## (6) Proof of (K1')

This repeats (1) of `spectral-gap-ratio-kill-proof`, with (A) in place of the
regular import. On `x in L`, put `λ = min(λ_2, 1)` and `η = λ/X(s)`. Then
`opt >= 1 − η`, `λ = X(s) η >= 3η >= eη`, and (A) returns a labeling of value
`>= 1 − C_A log(X(s))/X(s) > s`. On `x ∉ L`, every labeling has value
`<= opt <= s`. So accepting iff the returned value exceeds `s` decides `L` in
polynomial time.

## (7) Proof of (G)

By the setting of `orientation-lifts-sandwich-2to1-game-values`, `U_o(G)` is a
unique game on the same weighted bipartite graph as `G`. So it is loop-free, with
`λ_2(U_o(G)) = λ_2(G) <= 1`. By its item 1, `opt(U_o(G)) = val(U_o(G)) <= val(G)`.

The map `x → U_o(R(x))` is polynomial-time. On YES it meets the hypothesis of
(K1') by assumption. On NO, `opt <= val(R(x)) <= s`. So (K1') gives `L in P`.

## (8) Checks

`check_degree_blowup.py` exits 0 after the following checks.

- *(A)* On 40 random loop-free weighted games (`n <= 5`, `k <= 3`): every copy
  has degree 1, and the blow-up spectrum equals `spec(U)` plus `N − n` ones, to
  `1e-8`.
- *(B)* `opt(H) = opt(U)` exactly, in rational arithmetic, by brute force on the
  cases with `N <= 11`.
- *(C)* The integer biregular construction on six hosts is regular of degree
  `d_A d_B/g`, with `λ_2` and `opt` preserved.
- *(D)* The containment host `V_(l−1) ∪ V_l` of `F_q^n`, for
  `q in {2,3}` and `n <= 5`, has `σ_2^2 = 1 − [n]/([l][n−l+1]) < 1/q`.
