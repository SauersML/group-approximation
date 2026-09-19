---
rg: 2
id: lift-witness-rules-below-cycle-scale-gauge-blindness-proof
kind: route
title: The gauge acts on right-hand sides by the column space, so a rule whose acceptance functions carry no Fourier mass on the cycle code has an orbit-independent average lift value, and a first-moment count makes the cycle scale linear while a volume count keeps NO orbits over the same matrix
target: lift-witness-rules-below-cycle-scale-are-gauge-blind
requires: []
artifacts:
  - experiments/ugc-witness-locality-2026-09-18/check_witness_locality.py
---

Notation is as in the target claim. The proof is self-contained apart from two
verbatim imports of instance structure, quoted in the claim, from
`view-local-branch-selectors-are-gauge-blind` and
`grassmann-composed-2to2-coarsenings-are-satisfiable`.

## Step 0 (the gauge acts by the column space)

`<m_j, A + z> + (b_j + <m_j, z>) = <m_j, A> + b_j`, so `A` satisfies equation `j`
of `I` iff `A + z` satisfies equation `j` of `I^z`. Therefore the 3LIN value is
constant on each coset `b + Im(M)`, and `Im(M)` is exactly the set of right-hand
sides of the satisfiable instances over `M`. The vertex set, subspaces, branch
vectors and weights of the lift do not move under the gauge, by the import.

## Step 1 (local gauge uniformity)

*Let `S` be a cycle-free set of equations. For every `b`, the restriction
`(b + Mz)|_S` with `z` uniform in `F_2^n` is uniform on `F_2^S`.*

The map `z |-> (Mz)|_S` is linear with image `V <= F_2^S`, and
```text
V^perp = { c in F_2^S : <c, (Mz)|_S> = 0 for all z }
       = { c in F_2^S : sum_(j in S) c_j m_j = 0 } = 0
```
by cycle freeness. So `V = F_2^S`, `(Mz)|_S` is uniform, and so is its
translate. In particular the law does not depend on `b`. Every `S` with
`|S| < d_cyc(M)` is cycle free, because a dependency inside `S` is a nonzero
cycle of weight at most `|S|`.

## Step 2 (the Fourier identity, and Theorem 1)

Fix an edge `e` and let `f_e : F_2^m -> {0,1}` be the indicator that the
labelling `W(b)` satisfies `e` in `U_(S(b))`. Expanding `f_e` in characters,
```text
E_z f_e(b + Mz) = sum_c hat f_e(c) (-1)^(<c,b>) E_z (-1)^(<c, Mz>)
                = sum_(c in ker(M^T)) hat f_e(c) (-1)^(<c,b>),
```
because `E_z (-1)^(<c, Mz>) = E_z (-1)^(<M^T c, z>)` is `1` if `M^T c = 0` and
`0` otherwise. The `c = 0` term is `hat f_e(0)`, which does not depend on `b`.
Hence for any `b, b'`,
```text
| E_z f_e(b + Mz) - E_z f_e(b' + Mz) |
      <= 2 sum_(0 != c in C^perp(M)) | hat f_e(c) |,
```
and summing against the weights gives Theorem 1,
`| E_z Val_(b+Mz) - E_z Val_(b'+Mz) | <= 2 Lambda(S, W)`.

If `D(S, W) < d_cyc(M)` then each `f_e` depends on `b` only through the
cycle-free set `S_e`, so `hat f_e` is supported on `Span(e_j : j in S_e)`. A
nonzero `c` in that span with `M^T c = 0` is a dependency inside `S_e`, which
cycle freeness forbids. So `Lambda(S, W) = 0` and the averages are equal
exactly. (Equivalently, apply Step 1 edge by edge: the acceptance probability of
`e` is the average of `f_e` over a uniform value of `b|_(S_e)`, a function of `M`
alone.)

Two remarks on the hypotheses. First, `W` must be one rule defined on all of
`F_2^m`, not a labelling supplied separately on each orbit; the `R`-local form
is automatically global. Second, the bound uses only the dependence of `W` on
the right-hand sides: `W` may depend on `M` arbitrarily, it need not be
computable, and the selector `S` need not be efficient.

## Step 3 (Theorem 2)

Write `F(b) = E_z Val_(b+Mz)(W)`. On the satisfiable orbit,
`Pr_z[Val >= 1/2 + gamma] >= 1 - eta` and `Val >= 0` give
`F(0) >= (1 - eta)(1/2 + gamma) >= 1/2 + gamma - eta`. By Step 2,
`F(b) >= F(0) - 2 Lambda` for every `b`. Put `p = Pr_z[Val_(b+Mz) >= 1/2 + gamma/2]`.
Since `Val <= 1`,
```text
F(b) <= p + (1 - p)(1/2 + gamma/2) <= 1/2 + gamma/2 + p/2,
```
so `p >= 2(F(b) - 1/2 - gamma/2) >= 2(gamma/2 - eta - 2 Lambda) = gamma - 2 eta - 4 Lambda`.
Finally `Val_b(W) <= val(U_(S(b)))` because `W(b)` is one labelling, which gives
the statement for the lift value.

## Step 4 (Theorem 3: a source with a linear cycle scale and NO orbits)

Let the rows `m_1, ..., m_m` be independent and uniform among the `C(n,3)`
weight-3 vectors, with `m = C n`.

*(a) Cycle scale.* Fix `w >= 2` and a set `S` of `w` rows. The event
`sum_(j in S) m_j = 0` says that in the multiset of `3w` variable slots every
variable occurs an even number of times. For odd `w` the number `3w` of slots is
odd and no such multiset exists, so the probability is `0`; take `w` even, so
that `3w/2` is an integer. Such an assignment of slots to
variables determines, injectively, a perfect matching of the `3w` slots together
with one variable per matched pair, so there are at most `(3w-1)!! n^(3w/2)`
even slot assignments; dividing by the `6^w` orderings inside the triples and
comparing with `C(n,3)^w >= (n/2)^(3w) / 6^w`,
```text
Pr[ sum_(j in S) m_j = 0 ] <= (3w-1)!! * 8^w * n^(-3w/2) <= [ 8 (3w/n)^(3/2) ]^w.
```
Hence, with `K = 8 e 3^(3/2) < 114`,
```text
E #{cycles of weight w} <= C(m,w) [8 (3w/n)^(3/2)]^w
                        <= [ (e m / w) * 8 * (3w/n)^(3/2) ]^w
                        =  [ K C (w/n)^(1/2) ]^w.
```
Take `delta = 1/(2 K C)^2`. For `w <= delta n` the bracket is at most `1/2`, so
the expected number of cycles of weight at most `delta n` is at most
`sum_(w >= 2) 2^(-w) = 1/2`. By Markov, `d_cyc(M) > delta n` with probability at
least `1/2`.

*(b) NO orbits.* The 3LIN value of `b` is `1 - min_z |b + Mz| / m`, so
`val(b) > 1/2 + eps` iff `b` lies within Hamming distance `(1/2 - eps) m` of
`Im(M)`. The number of such `b` is at most
`2^n * sum_(i <= (1/2-eps)m) C(m,i) <= 2^(n + m H(1/2 - eps))`. With
`H(1/2 - eps) <= 1 - 2 eps^2 / ln 2` and `n = m / C`, this is less than
`2^(m-1)` as soon as `1/C < 2 eps^2 / ln 2`. All cosets of `Im(M)` have the same
size, so more than half of them consist of instances of 3LIN value at most
`1/2 + eps`. This holds for every `M`, in particular for one supplied by (a).

Both conclusions hold together with probability at least `1/2 - o(1)`, so such
an `M` exists. Gallager's minimum-distance theorem for `(3, 3C)`-regular
low-density ensembles gives a better constant in (a); it is not needed, and the
count above keeps the claim free of imports. Row weight 3 makes the rows
distinct with probability `1 - O(1/n)`, and a regular variant is obtained by
conditioning on the variable degrees, which changes neither count by more than a
constant factor.

## Step 5 (why the natural strengthening fails: the decoupling attack)

One would like an absolute bound, not only an orbit-independent one. The lift is
a unique game: on an accepted edge the A-label determines the B-label, so
```text
val(U_o) <= sum_(a in A) max_(sigma in Lab(a)) sum_(e in a) w_e
              [ branch condition of e holds for sigma ],
```
which replaces a maximum over exponentially many labellings by a sum of
independent maxima over label sets of constant size. Each summand is local in
`b`, so by Step 2 its average is orbit independent, and if the branch conditions
behaved like independent fair coins the bound would be `1/2 + O((l/deg)^(1/2))`
and would kill the hole outright.

**It dies.** The decoupling throws away B-consistency, and the selector can then
make the branch condition hold everywhere at once. In the folded picture the
branch condition at `e` for the folded label `sigma` reads
`sigma(r x_e) + c_e(b) = g_e(view_e(b))(tau)` where the offset `c_e(b)` is a
function of `b|_(W_e)`, and `W_e` is inside the selector's own view. Choosing
`g_e(view)(tau) := c_e(view)` makes the branch condition true for the folded
zero label at every edge, so the decoupled bound equals `1` identically. The
artifact confirms this: `--mode decouple` reports `0` violations of the
inequality over all `2^9` right-hand sides of a tiny instance, and reports that
with the offset-cancelling selector the minimum of the decoupled bound over all
`b` is `1`.

So any absolute bound must keep the B-vertex consistency constraint, which is
exactly the Grassmann agreement structure that the Khot--Minzer--Safra expansion
theorem governs. That is recorded as the open need `H2-absolute` in the target
claim's attempts.

## Step 6 (the artifact)

`experiments/ugc-witness-locality-2026-09-18/check_witness_locality.py` builds
an abstract locally gauged lift with the structure the proof uses and nothing
else: an A-vertex carries one window equation, a B-vertex carries one, the
A-labels are `F_2^2` and the B-labels `F_2^1`, the agreement offset and the
branch offset are linear in the two window right-hand sides, and the selector's
orientation is an arbitrary function of the two window right-hand sides and the
B-label. It then enumerates every gauge of every coset of `Im(M)` and compares
exact averages. Results are quoted in the claim's `## Check`.
