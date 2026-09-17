---
rg: 2
id: walsh-frame-rich-2to1-value-proof
kind: route
title: Perfect SDP value forces pair-sum identities, pair sums of twisted characters share their difference, a forcing difference set makes the twist a character, and one common vector per component labels every forcing edge
target: walsh-frame-rich-2to1-games-have-value-near-one
requires: []
artifacts:
  - experiments/rich-2to1-walsh-frames-2026-09-17/walsh_frame_enrichment_check.py
---

Notation is as in the target claim. All vectors live in `R^K`, with coordinates
indexed by `F_2^k`. For `x in F_2^k`, `chi_c(x) = (-1)^(c.x)`.

**Step 0 (pair-sum identity).** Each edge contributes at most 1, and the weights
are positive, so a perfect solution has contribution 1 on every edge.

Fix an edge `(u,v)`. Put `Y_b = sum_(a in pi_(uv)^(-1)(b)) z(u,a)` and
`z_b = z(v,b)`. The `Y_b` are sums over disjoint sets of orthogonal vectors, so
they are orthogonal and `sum_b |Y_b|^2 = sum_a |z(u,a)|^2 = 1`. The contribution
of the edge is `sum_b <Y_b, z_b>`, and

`sum_b <Y_b, z_b> <= sum_b |Y_b| |z_b| <= (sum_b |Y_b|^2)^(1/2) (sum_b |z_b|^2)^(1/2) = 1`.

Equality in the first step means each `z_b` is a nonnegative multiple of `Y_b`.
Here `Y_b != 0`, because it is a sum of two orthogonal nonzero vectors. Equality
in the second step means `|z_b| = |Y_b|` for all `b`. Hence

`z(v,b) = z(u,a) + z(u,a')` whenever `pi_(uv)^(-1)(b) = {a,a'}`.

**Step 1 (differences are shared).** Let `u` and `g` be neighbours of `v`. Fix a
right label `b`, and write

* `{c, c+gamma} = psi_u(pi_(uv)^(-1)(b))`,
* `{c', c'+gamma'} = psi_g(pi_(gv)^(-1)(b))`,

where `gamma` and `gamma'` are nonzero. By Step 0,

`K z(v,b) = f_u chi_c (1 + chi_gamma) = f_g chi_(c') (1 + chi_(gamma'))`.

The factors `f_u chi_c` and `f_g chi_(c')` take values `+-1`, and
`1 + chi_gamma` takes values in `{0, 2}` and vanishes exactly off `gamma^perp`.
So the left side has support `gamma^perp` and the right side has support
`gamma'^perp`. Distinct nonzero vectors have distinct orthogonal hyperplanes, so
`gamma = gamma'`.

Hence the map `b -> gamma_b` is the same at every neighbour of `v`, and
`Gamma(P_(uv)) = {gamma_b : b}` depends only on `v`. Dividing by 2 on
`gamma_b^perp` gives

`h := f_u f_g = chi_(c + c')` on `gamma_b^perp`, for every `b`.   (1)

**Step 2 (hyperplane-character lemma).** Write `h = (-1)^H` with
`H : F_2^k -> F_2`.

* `0 in gamma_b^perp`, so (1) gives `H(0) = 0`.
* On each `gamma_b^perp`, `H(x) = (c + c').x`, so `H` is additive there.

If `Gamma(P_(uv))` is forcing, `H` is linear, say `H(x) = delta.x`. Then
`f_g = f_u chi_delta`, and since `psi_g` is a bijection,

`{z(g,a) : a} = {f_u chi_(delta + d) / K : d in F_2^k} = {z(u,a) : a}`.

This proves item 1.

*A sufficient condition.* Suppose `Gamma` meets every codimension-2 subspace.
Take distinct nonzero `x` and `y`; they are linearly independent over `F_2`. So
`{x,y}^perp` has codimension 2 and contains some `gamma in Gamma`. Then `x`, `y`
and `x + y` lie in `gamma^perp`, and `H(x+y) = H(x) + H(y)`. The cases `x = y`,
`x = 0` and `y = 0` are immediate from `H(0) = 0`. So `H` is additive, hence
linear, and `Gamma` is forcing.

The converse fails. The artifact finds 57 forcing sets in `F_2^3` but only one
that meets every codimension-2 subspace.

**Step 3 (rigid labelling, item 2).** Call a right vertex *forcing* if its
difference set is forcing; by Step 1 this is well defined.

Form a graph on left vertices by joining any two neighbours of a forcing right
vertex. By Step 2, along every path the vector set is constant, so each
component `C` has a common vector set `S_C`. This set consists of `K` nonzero,
pairwise orthogonal vectors, hence is linearly independent.

Choose `w_C in S_C`, and label as follows.

* For `u in C`, let `L_u` be the unique `a` with `z(u,a) = w_C`. It exists
  because `{z(u,a)} = S_C`, and it is unique because `psi_u` is a bijection.
* For a forcing `v`, all neighbours lie in one component `C`. Pick a neighbour
  `u` and put `M_v = pi_(uv)(L_u)`.
* Label every other right vertex arbitrarily.

*Every edge at a forcing `v` is satisfied.* Let `g` be another neighbour of `v`.
Put `b = M_v`, and write `pi_(uv)^(-1)(b) = {L_u, a'}` and
`pi_(gv)^(-1)(b) = {p, q}`. By Step 0,

`w_C + z(u,a') = z(v,b) = z(g,p) + z(g,q)`.

All four vectors lie in the linearly independent set `S_C`, so
`{w_C, z(u,a')} = {z(g,p), z(g,q)}`. Hence `w_C in {z(g,p), z(g,q)}`, so
`L_g in {p,q}` and `pi_(gv)(L_g) = b`.

So the labelling satisfies every edge at a forcing right vertex, and
`val(G) >= w(forcing edges)`.

**Step 4 (richness).** The edge distribution chooses a left vertex from its
marginal and then an incident edge from the conditional law. Richness says the
induced pairing of `[K]` is uniform over perfect pairings. Transport by the
bijection `psi_u` preserves uniformity, so `P_(uv)` is a uniform pairing of
`F_2^k`. Therefore `w(non-forcing edges) = E_u Pr[P not forcing] = q_K`, and
Step 3 gives `val(G) >= 1 - q_K`.

**Step 5 (bound on `q_K`).** Let `m = K/4`. If `Gamma(P)` is not forcing, then
by Step 2 it misses some codimension-2 subspace `W`. A pair `{c, c'}` has
`c + c' in W` iff it lies inside a coset of `W`, so no pair of `P` lies inside a
coset of `W`.

The subspaces `W = {x,y}^perp` correspond to the 2-dimensional subspaces
`span{x,y}`. There are `(K-1)(K-2)/((4-1)(4-2)) = (K-1)(K-2)/6` of them. Take a
union bound over `W`.

For a fixed `W`, fix one coset `A`, of size `m`, and bound
`Pr[no pair inside A]`. Generate the uniform pairing sequentially: at each step
take the least unmatched element of `A` and match it to a uniformly random other
unmatched element. Any rule that chooses the next element from the history
yields the uniform pairing.

Suppose the first `j` steps all matched outside `A`. Then `K - 2j` elements are
unmatched, `m - j` of them in `A`. The current element's partner is uniform
among the other `K - 2j - 1`, of which `m - j - 1` lie in `A`. So the partner
avoids `A` with probability

`r(j) = (K - m - j)/(K - 2j - 1) = (3m - j)/(4m - 1 - 2j)`.

Stop after `ceil(m/2)` steps. Then

`Pr[no pair inside A] <= prod_(j < ceil(m/2)) r(j)`, and so `q_K <= B(K)`.

*Closed form.* The derivative of `r` has the sign of
`-(4m-1-2j) + 2(3m-j) = 2m + 1 > 0`, so `r` is increasing. For
`j <= ceil(m/2) - 1 < m/2`, `r(j) <= r(m/2) = (5m/2)/(3m-1)`. This is `<= 7/8`
iff `m >= 7`. So for `K >= 32` (`m >= 8`),
`B(K) <= (K^2/6)(7/8)^(K/8)`.

The artifact evaluates the product exactly as `B(512) = 0.01074...`. For
`K >= 1024`, `(K^2/6)(7/8)^(K/8)` is decreasing, since
`d/dK [2 ln K + (K/8) ln(7/8)] = 2/K - 0.0167 < 0`, and at `K = 1024` it equals
`0.0066`. Hence `q_K <= 0.0108` for every power of two `K >= 512`. This proves
item 3.

**Step 6 (item 4).** Choose every left label and right label independently and
uniformly. An edge is satisfied with probability
`Pr[pi_(uv)(a) = b] = 2/K`, so `val(G) >= 2/K`.

* For `K <= 256`, `val(G) >= 1/128 > delta`.
* For `K >= 512`, Step 5 gives `val(G) >= 1 - 0.0108 > delta`.

**GKOPTW is Walsh-framed and coset-paired.** GKOPTW Section 5.2 defines
"z(Pi,α)(x) := 1/K ([Pf]χα)(x)" with `[Pf] : F_2^k -> {-1,1}`. This is a Walsh
frame with `psi` the identity.

Their right vertex `Q^γ_i` has labels identified with "F_2^k/⟨γ⟩", and the
constraint is `A(Pf) + α ∈ B(Qγf) + β`. So every edge pairing is the coset
pairing of `<gamma>`, and `Gamma(P_(uv)) = {gamma}`.

A single hyperplane is never forcing for `k >= 2`. Take `H` equal to 1 at one
point outside `gamma^perp` and 0 everywhere else. It is additive on
`gamma^perp`. It is not linear: the only linear functions vanishing on
`gamma^perp` are 0 and `x -> gamma.x`, and the latter is 1 on all
`K/2 >= 2` points outside `gamma^perp`. So
the GKOPTW gap sits entirely on non-forcing edges, consistent with item 2 and
with their `O(1/sqrt(log K))` soundness. `QED`
