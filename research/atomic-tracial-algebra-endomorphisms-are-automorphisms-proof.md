---
rg: 2
id: atomic-tracial-algebra-endomorphisms-are-automorphisms-proof
kind: route
title: Stationary mass on the Bratteli inclusion matrix forces a block-preserving bijection
target: atomic-tracial-algebra-endomorphisms-are-automorphisms
requires: []
---

Let `Q = theta(P) <= P`.  Since `theta` is a trace-preserving isomorphism onto
`Q`, the algebra `Q` is atomic with the same data: blocks `Q_j ~= M_(n_j)`
indexed by the same `I`, minimal-projection traces `mu_j`, weights
`lambda_j = n_j mu_j`.

**Inclusion matrix.**  For each `P`-block `i` and `Q`-block `j` let
`m_(ij) in Z_(>= 0)` be the multiplicity with which the irreducible
representation of `Q_j` occurs in the restriction to `Q` of the defining
representation of `P_i = M_(n_i)` on `C^(n_i)`.  Unitality of the inclusion
gives the dimension count and the trace of a minimal projection `f_j` of `Q_j`,
computed in `P`, gives the mass count:

```text
n_i  = sum_j m_(ij) n_j          (row condition),                     (AT1)
mu_j = sum_i m_(ij) mu_i         (column condition, tau(f_j) two ways). (AT2)
```

Rows are finitely supported by (AT1).

**A Markov chain.**  Put `Q_(ij) = m_(ij) n_j / n_i`.  By (AT1) the matrix
`(Q_(ij))` is row-stochastic on the countable state space `I`.  By (AT2),

```text
sum_i lambda_i Q_(ij) = sum_i n_i mu_i m_(ij) n_j / n_i = n_j mu_j = lambda_j,
```

so `lambda` is a stationary probability distribution for this chain, and it
charges every state.  A state charged by a stationary distribution is positive
recurrent (for a transient or null-recurrent state `j` one has
`p^((n))_(ij) -> 0` for every `i`, and then `lambda_j = sum_i lambda_i
p^((n))_(ij) -> 0` by dominated convergence).  Hence every state is recurrent,
and consequently whenever `j` is reachable from `i`, `i` is reachable from `j`.

**Block sizes are constant along edges.**  If `Q_(ij) > 0` then `m_(ij) >= 1`
and (AT1) gives `n_i >= m_(ij) n_j >= n_j`: `n` is non-increasing along every
edge.  By recurrence every edge `i -> j` lies on a cycle through `i`, along
which `n` cannot decrease and return, so `n_j = n_i` for every `j` with
`m_(ij) > 0`.  Then (AT1) reads `n_i = n_i sum_j m_(ij)`, so each row has
exactly one nonzero entry, equal to `1`.  Thus `M = (m_(ij))` is the matrix of
a map `T : I -> I`, `m_(i,T(i)) = 1`, with `n_(T(i)) = n_i`, and (AT2) reads

```text
mu_j = sum_(i : T(i) = j) mu_i.                                       (AT3)
```

**`T` is a bijection.**  Surjective: `mu_j > 0` forces `T^(-1)(j)` nonempty.
Along a forward orbit `i, T(i), T^2(i), ...` the weights are non-decreasing by
(AT3), and block sizes are constant, so `lambda_(T^k(i)) >= lambda_i > 0` for
all `k`.  If the orbit never repeated, infinitely many distinct states would
carry mass at least `lambda_i`, contradicting `sum lambda = 1`.  So every
forward orbit is eventually periodic.  Around a cycle `c_0 -> c_1 -> ... ->
c_0` the weights are non-decreasing and return, hence constant, so by (AT3)
every fibre `T^(-1)(c_(k+1))` is the singleton `{c_k}`.  If some `i` were not
on a cycle, the first point of its orbit lying on a cycle would have a fibre
containing both its cycle predecessor and a point off the cycle -- two
elements -- contradicting the previous sentence.  Hence every point lies on a
cycle, all fibres are singletons, and `T` is a bijection with
`n_(T(i)) = n_i`, `mu_(T(i)) = mu_i`.

**Conclusion.**  Column `T(i)` of `M` has its only nonzero entry in row `i`,
with `m_(i,T(i)) = 1` and `n_(T(i)) = n_i`: the block `Q_(T(i)) ~= M_(n_i)`
sits unitally inside `P_i ~= M_(n_i)` and nowhere else, so `Q_(T(i)) = P_i` and
the unit of `Q_(T(i))` is the central projection `z_i` of `P`.  Since `T` is
onto, every block of `P` is a block of `Q`, i.e. `Q = P`.
