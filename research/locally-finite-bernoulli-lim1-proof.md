---
rg: 2
id: locally-finite-bernoulli-lim1-proof
kind: route
title: Fresh-block cocycles defeat every telescoping trivialization by characteristic-function decay
target: locally-finite-bernoulli-first-l0-cohomology-nonzero
requires: []
---

Fix an exhausting chain `G_0 = 1 <= G_1 <= ...` of finite subgroups.
Write `V = L^0(Y,R)`, `A_n = V^(G_n)`, and `P_n f = |G_n|^(-1)
sum_(g in G_n) g.f` (defined on ALL of `L^0`; on bounded functions it
is the conditional expectation onto the `G_n`-invariant sigma-algebra
`B_n`, because the finite action is essentially free, so the
conditional law given `B_n` is uniform on orbits).

**Step 1 (Milnor).**  The bar cochain complexes satisfy
`C^*(G, V) = lim C^*(G_n, V)` with surjective restrictions, giving
`0 -> lim^1 H^(q-1)(G_n,V) -> H^q(G,V) -> lim H^q(G_n,V) -> 0`.
Since `V` is a uniquely divisible and `G_n` finite,
`H^q(G_n,V) = 0` for `q >= 1`; hence `H^1(G,V) = lim^1 {A_n}`.

**Step 2 (the cocycle data).**  `lim^1 {A_n} != 0` iff some
`(e_n)`, `e_n in A_n`, admits no solution of `t_n - t_(n+1) = e_n`
with `t_n in A_n`.  Choose the data as follows.  Pick pairwise
distinct free `G`-orbits `O(k,i)` in `I` (`k >= 0`, `1 <= i <= N_k`,
`N_k` specified below), identify each with `G`, and let the
`(k,i)`-block be the subset `G_(k+1) c G` of that orbit.  Its
`G_k`-cosets partition it into sub-blocks; fix two of them and let
`F_(1,i), F_(2,i)` be the fair `+-1` signs
`sign(sum_(u in sub-block)(x_u - 1/2))`, which are `G_k`-invariant.
Set `e_k = sum_i (F_(1,i) - F_(2,i))`.  Then `e_k in A_k`, and
`P_(k+1) e_k = 0` because averaging over `G_(k+1)` sends every
`F_(j,i)` to the same symmetrized average over all sub-blocks.

**Step 3 (rigidity of solutions).**  `P_n e_k = P_n P_(k+1) e_k = 0`
for `k < n`, so `S_n := e_0 + ... + e_(n-1)` satisfies `P_n S_n = 0`.
If `(t_n)` solves the telescope then `t_0 = S_n + t_n` with
`t_n in A_n`, and applying `P_n` gives `t_n = P_n t_0`: the solution
is DETERMINED by `t_0`, and `t_0 = S_n + P_n t_0` for every `n`.

**Step 4 (characteristic-function decay).**  For real `s`,
`phi(s) := E[e^(i s t_0)] = E[E[e^(i s S_n)|B_n] e^(i s P_n t_0)]`
(the second factor is `B_n`-measurable and bounded), so `|phi(s)|^2
<= E|E[e^(i s S_n)|B_n]|^2 = |G_n|^(-1) sum_(u in G_n)
E[e^(i s (u.S_n - S_n))]`.  Fix `u != 1` and let `k_0(u) = min{k : u
in G_(k+1)}`.  For `k >= k_0`, `u` preserves each level-`k` block, so
`u.e_k - e_k` is a function of the level-`k` blocks; for `k < k_0`,
`u.(block)` is disjoint from every designated block (inside one free
orbit, `u G_(k+1) cap G_(k+1) = empty` since `u` is not in
`G_(k+1)`; across orbits, disjointness is automatic), so `u.e_k` is
an independent copy of `e_k`.  Hence the summands over `k` are
independent and

```text
|E[e^(i s (u.S_n - S_n))]| <= prod_(k < k_0(u)) |phi_(e_k)(s)|^2
                            = prod_(k < k_0(u)) (cos^2 s)^(2 N_k).
```

Since `#{u : k_0(u) <= K} = |G_(K+1)|`, choosing `N_k` growing fast
enough (e.g. `N_k >= k (k + log|G_(k+2)|) sup_(s in S_k)
(1 - cos^2 s)^(-1)` along an exhaustion `S_k` of a countable dense
set of `s` avoiding `pi Z`) makes
`|G_n|^(-1) sum_u prod_(k<k_0(u)) (cos^2 s)^(2N_k) -> 0` for every
fixed `s` outside `pi Z`.  So `phi(s) = 0` there; but `phi` is the
characteristic function of an a.e.-finite random variable, hence
continuous with `phi(0) = 1` -- contradiction.  No `t_0` exists, and
`lim^1 {A_n} != 0`.

**Step 5 (equivariance and the corollary).**  If a finite group `T`
normalizes every `G_n`, run the construction with blocks in distinct
`(T . G)`-orbits and replace `e_k` by `sum_(t in T) t.e_k`: the data
becomes `T`-invariant, the summands stay independent (free orbits
separate the `T`-translates), and Step 4 reruns over the chain
`T . G_n` with `k_0(u) = infinity` whenever `u` has a nontrivial
`T`-part -- those terms are only smaller.  For the corollary:
`P_K^- = L_K x| (locally finite unipotent part)` is locally finite,
acts freely on `I = Lambda` by left translation (so every orbit is
free), and has infinite index in `Lambda` (else `Lambda` would be
locally finite), giving infinitely many orbits.  The base `[0,1]` is
diffuse, so each sub-block hosts the required fair signs.
