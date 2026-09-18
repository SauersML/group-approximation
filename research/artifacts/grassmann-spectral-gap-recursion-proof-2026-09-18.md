# Read the Grassmann adjacency off the down-up and up-down walks between two levels, use that D*D and DD* share their nonzero spectrum, and telescope the resulting one-step recursion from the complete graph at level one

*Attempt artifact (2026-09-18), formerly route `grassmann-spectral-gap-recursion-proof`
into `grassmann-graphs-have-constant-normalized-spectral-gap`, requires [].
Demoted from the graph at landing because all three swarm-0917 referee lenses
returned `refuted` on the parent result
`unique-games-hard-on-non-sse-grassmann-constraint-graphs`. The refutation is
**not** aimed at the contents of this file: all three lenses re-derived
Theorems 1-6 by hand and confirmed them, and the replay
`experiments/grassmann-spectral-gap-2026-09-17/check_grassmann_gap.py` prints
`ALL PASS`, exit 0. What was refuted is the small-set-expansion gloss that the
target claim carried in its "What this fixes, in one line" paragraph, which is
not proved anywhere below. Restore this as a route once the target claim is
restated without that gloss and a full referee pass survives.*

Notation is that of the target claim. `[m] = (q^m - 1)/(q - 1)`, `V_j` carries
the uniform probability measure, `A_1^(l)` is the 0/1 adjacency of
`Gr_q(n,l)` and `Ahat_l = A_1^(l)/d_1^(l)` its normalized adjacency. Write
`t_l` for the second largest eigenvalue of `Ahat_l` and `s_l = 1 - t_l`, so
`s_l = lambda_2(Gr_q(n,l))`.

## (0) Counting

Fix `1 <= l <= n - 1`.

* an `l`-space `L` has `[l]` hyperplanes `M subset L`;
* an `(l-1)`-space `M` lies in `[n-l+1]` many `l`-spaces (the `1`-spaces of
  `F_q^n / M`, a space of dimension `n - l + 1`);
* hence the number of incident pairs is `|V_(l-1)| [n-l+1] = |V_l| [l]`;
* `[n-l+1] - 1 = (q^(n-l+1) - q)/(q-1) = q [n-l]`, and `[l] - 1 = q [l-1]`.

*Degree and loop-freeness.* `L ~ L'` needs `L != L'`, so there are no loops.
Given `L`, every neighbour `L'` determines `M = L cap L'`, a hyperplane of `L`,
and conversely a hyperplane `M subset L` together with an `l`-space `L' ⊋ M`,
`L' != L`, gives a neighbour. So `Gr_q(n,l)` is regular of degree
`d_1 = [l] ([n-l+1] - 1) = q [l] [n-l]`, which is Theorem 1 apart from
connectivity (proved in (3)).

## (1) Two walks between adjacent levels

Assume `2 <= l <= n - 1`. Define

```text
D : L^2(V_l) -> L^2(V_(l-1)),   (Df)(M)  = (1/[n-l+1]) sum_(L ⊃ M) f(L),
U : L^2(V_(l-1)) -> L^2(V_l),   (Ug)(L)  = (1/[l])     sum_(M ⊂ L) g(M).
```

*`U = D^*`.* With the uniform measures,

```text
<Df, g> = (1/(|V_(l-1)| [n-l+1])) sum_(M ⊂ L) f(L) g(M),
<f, Ug> = (1/(|V_l| [l]))         sum_(M ⊂ L) f(L) g(M),
```

and the two prefactors agree by the incidence count of (0). So `UD = D^* D`
and `DU = D D^*` are positive semidefinite self-adjoint operators, both fixing
the constant function `1` with eigenvalue `1` (`D1 = 1`, `U1 = 1`).

*`UD` is the Grassmann walk at level `l`.* For `f` on `V_l`,

```text
(UDf)(L) = (1/([l][n-l+1])) sum_(M ⊂ L) sum_(L' ⊃ M) f(L').
```

The term `L' = L` occurs once for each of the `[l]` hyperplanes `M`, total
weight `[l]/([l][n-l+1]) = 1/[n-l+1] =: alpha_l`. For `L' != L`, `M ⊆ L cap L'`
and `M ⊊ L` force `dim(L cap L') = l - 1` and `M = L cap L'`, so each neighbour
of `L` occurs exactly once, with weight `1/([l][n-l+1])`. There are `d_1`
neighbours and `d_1/([l][n-l+1]) = q[n-l]/[n-l+1] = 1 - alpha_l`. Hence

```text
UD = alpha_l I + (1 - alpha_l) Ahat_l,          alpha_l = 1/[n-l+1].       (1)
```

*`DU` is the Grassmann walk at level `l-1`.* Symmetrically, for `g` on
`V_(l-1)`,

```text
(DUg)(M) = (1/([l][n-l+1])) sum_(L ⊃ M) sum_(M' ⊂ L) g(M').
```

`M' = M` occurs once for each of the `[n-l+1]` spaces `L ⊃ M`, total weight
`1/[l] =: gamma_l`. For `M' != M`, `M + M' ⊆ L` and `dim(M + M') <= l` force
`dim(M cap M') = l - 2` and `L = M + M'`, so each `Gr_q(n,l-1)`-neighbour of
`M` occurs exactly once with weight `1/([l][n-l+1])`; there are
`d_1^(l-1) = q[l-1][n-l+1]` of them and
`d_1^(l-1)/([l][n-l+1]) = q[l-1]/[l] = 1 - gamma_l`. Hence

```text
DU = gamma_l I + (1 - gamma_l) Ahat_(l-1),      gamma_l = 1/[l].           (2)
```

Both identities are replayed as matrices in (C6).

## (2) The recursion

`D^*D` and `DD^*` have the same nonzero eigenvalues with the same
multiplicities. Both are PSD with top eigenvalue `1`. Let `b` be the second
largest eigenvalue of `DD^*` and `b'` that of `D^*D`. If `b > 0` then `b` is a
nonzero eigenvalue of `DD^*`, hence of `D^*D`, so `b' >= b`; the same argument
with the roles exchanged gives `b >= b'` when `b' > 0`. If `b = 0` then the only
nonzero eigenvalue of `DD^*` is `1`, hence the only nonzero eigenvalue of
`D^*D` is `1`, so `b' = 0`. In every case `b = b'`.

The maps `x -> alpha + (1-alpha)x` and `x -> gamma + (1-gamma)x` are increasing
and fix `1`, and in (1), (2) the top eigenvector is the same constant function
on both sides. So the second largest eigenvalues transform the same way, and
`b = b'` reads

```text
alpha_l + (1 - alpha_l) t_l  =  gamma_l + (1 - gamma_l) t_(l-1),
```

that is, subtracting from `1`,

```text
(1 - alpha_l) s_l  =  (1 - gamma_l) s_(l-1),        2 <= l <= n - 1.       (3)
```

With `1 - alpha_l = q[n-l]/[n-l+1]` and `1 - gamma_l = q[l-1]/[l]`,

```text
s_l = s_(l-1) ([l-1] [n-l+1]) / ([l] [n-l]).                               (4)
```

## (3) Base case, telescoping, Theorem 2

At `l = 1`, `dim(L cap L') = 0` for distinct `1`-spaces, so `Gr_q(n,1)` is the
complete graph on `[n]` vertices. Its normalized adjacency is `(J - I)/([n]-1)`
with eigenvalues `1` (simple) and `-1/([n]-1)`, so

```text
s_1 = 1 + 1/([n] - 1) = [n]/([n] - 1) = [n]/(q[n-1]),
```

using `[n] - 1 = q[n-1]`. This is the claimed formula at `l = 1`. Since
`0 < 1 - alpha_l, 1 - gamma_l < 1`, (3) gives `s_l > 0` for every `l` by
induction, i.e. `Gr_q(n,l)` is connected and the top eigenvalue is simple; this
completes Theorem 1. Telescoping (4) from `l = 1`,

```text
s_l = ([n]/(q[n-1])) prod_(j=2)^l ([j-1][n-j+1])/([j][n-j])
    = ([n]/(q[n-1])) ([1]/[l]) ([n-1]/[n-l])
    = [n] / (q [l] [n-l]),
```

because both products telescope. That is Theorem 2. (Checked against the
numerically computed spectra of six Grassmann graphs in (C1)--(C2), against the
classical `theta_1` in (C3), and as exact rationals in (C5).)

## (4) Theorem 3: the uniform floor

Multiply numerator and denominator by `(q-1)^2`:

```text
lambda_2 = (q-1)(q^n - 1) / ( q (q^l - 1)(q^(n-l) - 1) ).
```

Since `1 <= l <= n-1`, `(q^l - 1)(q^(n-l) - 1) = q^n - q^l - q^(n-l) + 1` and
`q^l + q^(n-l) >= 2q > 2`, so `(q^l-1)(q^(n-l)-1) < q^n - 1` and

```text
lambda_2 > (q-1)(q^n-1)/(q(q^n-1)) = (q-1)/q >= 1/2.
```

As `l` and `n - l` grow, `q^l + q^(n-l) = o(q^n)` and `lambda_2 -> (q-1)/q`.
Verified as exact rationals for `q <= 9`, `n < 60` in (C4b).

## (5) Theorem 4: the expansion floor and its equality cases

*The floor.* Let `G` be any weighted graph with normalized adjacency `Ahat`
(with respect to the degree measure `pi`), `S` a set, `mu = pi(S)`, `f = 1_S`.
Split `f = mu . 1 + g` with `<g, 1>_pi = 0`, so `||g||_pi^2 = mu(1-mu)`. Then

```text
(1 - Phi(S)) mu = <f, Ahat f>_pi = mu^2 + <g, Ahat g>_pi
                <= mu^2 + (1 - lambda_2) mu (1 - mu),
```

hence `1 - Phi(S) <= mu + (1 - lambda_2)(1 - mu)` and
`Phi(S) >= (1 - mu) lambda_2`. (This is the contrapositive of bullet (K4) of
`spectral-gap-ratio-reductions-cannot-prove-ugc`, repeated here so that this
route needs nothing.) Equality holds iff `g` lies in the eigenspace of the
second largest eigenvalue.

*Zoom-ins.* Fix `x != 0` and put `Z_x = {L in V_l : x in L}`. The `l`-spaces
containing `x` correspond to the `(l-1)`-spaces of `F_q^n/<x>`, so
`|Z_x| = [n-1 choose l-1]_q` and `mu(Z_x) = [l]/[n]` (the chance a uniform
`l`-space contains a fixed nonzero vector is `([q^l - 1]/(q-1))/([q^n-1]/(q-1))`).
For `L in Z_x`, a uniform neighbour `L'` is obtained by taking a uniform
hyperplane `M subset L` and then a uniform `l`-space `L' ⊋ M`, `L' != L`. If
`x in M` then `x in L'` always. If `x notin M` then, because `x in L` and
`dim M = l - 1`, `M + <x> = L`; any `L' ⊇ M` containing `x` would contain
`M + <x> = L`, hence equal `L`, which is excluded. So

```text
1 - Phi(Z_x) = Pr[x in M] = [l-1]/[l],     Phi(Z_x) = q^(l-1)/[l].
```

And `(1 - mu(Z_x)) lambda_2 = (([n] - [l])/[n]) . [n]/(q[l][n-l])`, where
`[n] - [l] = (q^n - q^l)/(q-1) = q^l [n-l]`, so it equals
`q^l[n-l]/(q[l][n-l]) = q^(l-1)/[l] = Phi(Z_x)`. Equality.

*Zoom-outs.* `L -> L^perp` (for any fixed nondegenerate bilinear form, or the
annihilator in the dual space) is an isomorphism `Gr_q(n,l) -> Gr_q(n,n-l)`
carrying `Z^H = {L : L subset H}` to a zoom-in at level `n-l`. Theorem 2 is
symmetric under `l <-> n-l`, so `Phi(Z^H) = q^(n-l-1)/[n-l]` and equality holds
there too. Both equalities are replayed as exact rationals for `q <= 7`,
`n < 45` in (C7c), and the floor itself is checked on explicit graphs in (C7).

## (6) Theorem 5: domination

Let `Q_W(f) = sum_(u<v) W_(uv) (f_u - f_v)^2`. By Courant--Fischer for the
normalized Laplacian of a loop-free weighted graph with common weighted degree
`d` (see step (0) of `spectral-gap-ratio-kill-proof` for the Rayleigh form),

```text
lambda_2(W) = min { Q_W(f) / (d ||f||^2) : sum_u f_u = 0, f != 0 },
```

with `||f||^2 = sum_u f_u^2`. If `W >= c A_1` entrywise then
`Q_W(f) >= c Q_(A_1)(f) >= c d_1 lambda_2(Gr_q(n,l)) ||f||^2` for every mean-zero
`f`, so `lambda_2(W) >= c d_1 lambda_2(Gr_q(n,l))/d`. With
`rho = c d_1/d` and Theorem 3, `lambda_2(W) > rho (q-1)/q`. Replay (C8).

*Invariance remark.* `GL_n(F_q)` acts transitively on ordered pairs `(L, L')`
with `dim(L cap L') = l - 1`: extend a basis of `L cap L'` by one vector of `L`
and one of `L'` and then to a basis of `F_q^n`, and map one such frame to
another. So a `GL_n(F_q)`-invariant weighting supported on that relation is
constant on edges, i.e. a scalar multiple of `A_1`, and has `rho = 1`.

## (7) Theorem 6: the containment graph

Let `Inc` be the `V_l x V_(l-1)` incidence matrix and
`Nrm = Inc/sqrt([l][n-l+1])` its normalized biadjacency, so that the normalized
Laplacian of the bipartite graph has eigenvalues `1 +- sigma_i` with `sigma_i`
the singular values of `Nrm`. Then `Nrm Nrm^T = UD` and `Nrm^T Nrm = DU` in the
notation of (1), (2). By (2) and Theorem 2,

```text
sigma_2^2 = gamma_l + (1 - gamma_l) t_(l-1)
          = 1 - (1 - gamma_l) s_(l-1)
          = 1 - (q[l-1]/[l]) . [n]/(q[l-1][n-l+1])
          = 1 - [n]/([l][n-l+1]).
```

Clearing denominators as in (4),

```text
[n]/([l][n-l+1]) = (q-1)(q^n - 1) / ((q^l - 1)(q^(n-l+1) - 1)),
```

and `(q^l - 1)(q^(n-l+1) - 1) = q^(n+1) - q^l - q^(n-l+1) + 1`, while
`q (q^n - 1) = q^(n+1) - q`. Since `l >= 1` and `n - l + 1 >= 2`,
`q^l + q^(n-l+1) >= q + q^2 > q + 1`, so
`(q^l-1)(q^(n-l+1)-1) < q(q^n - 1)` and therefore
`[n]/([l][n-l+1]) > (q-1)/q`. Hence

```text
sigma_2^2 = 1 - [n]/([l][n-l+1]) < 1/q,      lambda_2 = 1 - sigma_2 > 1 - q^(-1/2).
```

Checked as exact rationals in (C9) and against computed singular values in the
same block. The graph is biregular with side degrees `[l]` and `[n-l+1]`, and
regular only when `|V_(l-1)| = |V_l|`.
