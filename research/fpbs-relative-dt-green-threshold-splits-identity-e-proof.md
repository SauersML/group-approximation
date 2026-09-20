---
rg: 2
id: fpbs-relative-dt-green-threshold-splits-identity-e-proof
kind: route
title: Keep the length-truncated DT iteration as a sum of chain returns instead of bounding it by an operator norm, compare parameters edge by edge, count words to recover the l2 threshold, and push the chain along the modular cocycle on nonunimodular graphs
target: fpbs-relative-dt-green-threshold-splits-identity-e
requires:
  - fpbs-quotient-dt-threshold-is-quotient-l2-threshold
  - fpbs-quotient-l2-threshold-sandwich
  - fpbs-amenable-quotient-normal-relative-threshold-is-pc
  - fpbs-relative-gap-along-any-subgroup-separates
  - fpbs-nonunimodular-level-sets-break-identity-e
  - fpbs-hutchcroft-nonunimodular-pc-below-pt
---

Complete written proof; the scripts in the target's artifacts only check
the tree formulas numerically. Notation as in the target. All functions are
nonnegative, `*` is convolution on `Q` (or on `Gamma`), and entrywise
inequalities survive convolution with nonnegative functions. Because `N` is
normal, `pi_*(f * g) = pi_* f * pi_* g`. Write `mu = mu_{S,p}`, `a = a_S`.

**Step 1 (item 1).** Steps 1-2 of
`fpbs-quotient-dt-threshold-is-quotient-l2-threshold-proof` give, with no
hypothesis on `p` or `S`, the entrywise bound
`sigma^N_p <= sum_k mu^{*k} * a` on `Q` (length-truncated DT iteration,
pushed forward, then monotone convergence). Evaluate at `e_Q`:
`sigma^N_p(e_Q) = sum_(x in N) tau_p(o,x) = chi^N_p`. ∎

**Step 2 (item 2).** `P_p(o <->_S u)` is the probability of an increasing
event, so it is nondecreasing in `p`, and
`nu_{S,p}(g) <= (p/p') nu_{S,p'}(g)`. The event depends only on the `m(S)`
edges inside `S`. For a configuration `omega` of those edges, the likelihood
ratio is `(p'/p)^(#open) ((1-p')/(1-p))^(#closed) <= (p'/p)^(m(S))`, so
`P_{p'}(o <->_S u) <= (p'/p)^(m(S)) P_p(o <->_S u)`, and
`nu_{S,p'} <= (p'/p)^(m(S)+1) nu_{S,p}`. Pushing forward preserves both
bounds. Convolving `k` times gives
`mu_{S,p}^{*k} * a <= (p/p')^k mu_{S,p'}^{*k} * a` and the reverse bound with
`(p'/p)^(k(m(S)+1))`, hence both rate inequalities.

Let `U = {p : some S has r_p(S) < 1}` and `V = {p : some S has D_p(S) < infinity}`.
The root test gives `U ⊆ V`. If `D_p(S) < infinity`, then `r_p(S) <= 1`, so
`r_{p'}(S) <= p'/p < 1` for every `p' < p`, and `[0,p) ⊆ U`. The first rate
inequality makes `U` closed downwards. The second makes it open: if
`r_p(S) < 1`, then `(p'/p)^(m(S)+1) r_p(S) < 1` for `p'` slightly above `p`.
Hence `U = [0, sup U)` and `sup U = sup V = p^G(N;G)`. ∎

**Step 3 (item 3).** `p_c <= p^Q` is part 3 of the sandwich.

*`p^Q <= p^G`.* Let `p < p^Q`. By item 2 of the quotient DT node, some ball
`S = B_R` has `||rho_Q(mu)|| < 1`. Then
`(mu^{*k} * a)(e_Q) <= ||rho_Q(mu)^k a||_2 <= ||rho_Q(mu)||^k ||a||_2`, which
is summable, so `D_p(S) < infinity` and `p <= p^G`.

*`p^G <= p_c(N;G)`.* If `D_p(S) < infinity`, then `chi^N_p < infinity` by
item 1. For `y in N`, left multiplication by `y` preserves `N` and the law,
so `E_p|K_y ∩ N| = chi^N_p < infinity`, and a.s. `|K_y ∩ N| < infinity`.
Every cluster meeting `N` is some `K_y` with `y in N`, and `N` is countable.
So a.s. no cluster meets `N` in infinitely many vertices, and
`p <= p_c(N;G)`. ∎

**Step 4 (item 4).** By item 3, `p^Q = p_c(N;G)` holds iff both inequalities
`p^Q <= p^G` and `p^G <= p_c(N;G)` are equalities.

*Amenable `Q`.* Part 3 of the sandwich gives `p^Q = p_c`, and
`fpbs-amenable-quotient-normal-relative-threshold-is-pc` gives
`p_c(N;G) = p_c`. The chain then collapses.

*Trivial `Q`.* Here `pi_*` is the total mass, so
`mu_{S,p} = phi_p(S) delta_e` with
`phi_p(S) = p sum_{uv in Delta S} P_p(o <->_S u)`. This is DT's boundary
quantity `phi_p(S)` (arXiv:1502.03050, Section 1), and DT prove
`p~_c = p_c` there. Also `a_S = |S| delta_e`, so
`D_p(S) = |S| sum_k phi_p(S)^k`, which is finite iff `phi_p(S) < 1`. Therefore
`p^G = sup{p : some S has phi_p(S) < 1}`, which is DT's `p~_c`. ∎

**Step 5 (item 5).** By Step 2, `p_c in U = [0, p^G)` iff `p_c < p^G`. Item 3
then gives `p_c < p^G <= p_c(N;G)`. `N` is infinite, so
`fpbs-relative-gap-along-any-subgroup-separates` gives
`p_c(N;G) <= p_u(G)`, and hence `p_c < p_u`. Under (E-a), a gap
`p_c < p_c(N;G) = p^G` puts `p_c` in `U`. ∎

**Step 6 (item 6).** Assume (E-a). Item 4 then reduces `E` to `p^G = p^Q`, and
by item 3 its failure is `p^Q < p^G`. Type (ii) is `p_c = p^Q < p_c(N;G)`,
which under (E-a) reads `p_c = p^Q < p^G`. Item 5 then gives an `S` with
`r_{p_c}(S) < 1`. Item 4 of the quotient DT node says some `S` has
`sp_Q(mu_{S,p_c}) < 1` iff `p_c < p^Q`. Since `p_c = p^Q`, every `S` has
`sp_Q(mu_{S,p_c}) >= 1`. ∎

**Step 7 (item 7).** Put `b = eps a` and `beta = mu + b`. Expanding,
`beta^{*n}` is the sum over all words `w in {mu, b}^n` of the ordered
convolution of the letters. Distinct words are distinct summands, and all
of them are nonnegative.

*Word count.* For `m >= 1`, the tuples `(k_1, ..., k_m)` index distinct
words `mu^{k_1} b mu^{k_2} b ... mu^{k_m} b`. So, entrywise,

```text
( sum_k mu^{*k} * b )^{*m} = sum_{k_1..k_m} mu^{*k_1} * b * ... * mu^{*k_m} * b
                           <= sum_n beta^{*n}.
```

*Consequences.* Step 1 gives `eps sigma^N_p <= sum_k mu^{*k} * b`. Hence
`eps^m sigma_p^{*m}(e_Q) <= G_eps` for every `m`. By part 1 of the sandwich,
`sigma_p^{*m}(e_Q) = chi^(N,m)_p` and
`||sigma^N_p||_Q = limsup_m (chi^(N,m)_p)^(1/m) <= 1/eps`. The case `m = 1`,
evaluated at `e_Q`, is `eps D_p(S) <= G_eps`.

*Converse.* Let `p < p^Q`. Item 2 of the quotient DT node gives `R` with
`||rho_Q(mu_{B_R,p})|| <= 1/2`. Take `eps = 1/(4|B_R|)`, so
`||rho_Q(eps a)|| <= eps ||a||_1 = 1/4`. Then `||rho_Q(beta)|| <= 3/4` and
`beta^{*n}(e_Q) = <rho_Q(beta)^n delta_e, delta_e> <= (3/4)^n`, so
`G_eps <= 4`.

*The two suprema.* The first part puts every `p` with a finite `G_eps` at
or below `p^Q`, and the converse reaches every `p < p^Q`. The formula for
`p^G` is its definition. For the restatement of (E-b): `p^G <= p^Q` holds
iff every `p` with some finite `D_p(S)` satisfies `p <= p^Q`. That is, every
`p' < p` has some `S'` and `eps > 0` with a finite `G_eps`. ∎

**Step 8 (item 8).** Conventions are those of
`fpbs-nonunimodular-level-sets-break-identity-e` and
`fpbs-hutchcroft-nonunimodular-pc-below-pt`:
`Delta(x,y) = |Stab_y x| / |Stab_x y|`, which is `Gamma`-invariant and
satisfies `Delta(x,y) Delta(y,z) = Delta(x,z)`, and
`delta(gamma) = Delta(o, gamma o)` is a homomorphism. Put `h(y) = Delta(o,y)`.
Now `nu_{S,p}` is a function on vertices,
`nu_{S,p}(v) = p sum_{ {u,v} in Delta S } P_p(o <->_S u)`, and `mu = h_* nu`,
`a = h_* 1_S` are finitely supported on `Lambda`, since `G` is locally
finite and `S` is finite. Convolution on `Lambda` is multiplicative.

*Cocycle.* For `gamma in Gamma` and any `y`, invariance and the cocycle give
`h(gamma y) = Delta(o, gamma o) Delta(gamma o, gamma y) = delta(gamma) h(y)`.
For each vertex `v`, fix `gamma_v` with `gamma_v o = v`, so that
`delta(gamma_v) = h(v)`. By induction,
`h(gamma_(v_1) ... gamma_(v_k) y) = h(v_1) ... h(v_k) h(y)`.

*Transitive DT recursion.* Let `tau^(n)` be connection by an open path with
at most `n` edges. For `x in S` bound `tau^(n)(o,x) <= 1`. For `x` not in `S`,
the proof of Step 1 of `fpbs-quotient-dt-threshold-is-quotient-l2-threshold-proof`
applies word for word. Let `C` be the cluster of `o` inside `S`, `u` the last
vertex of the path in `C` and `v` the next one. Condition on `C = A`; the
rest of the path runs from `v` to `x` off `A` with at most `n-1` edges, and it
uses only edges independent of `{C = A}`. That proof uses no group
structure until its last line, where `tau^(n-1)(v,x)` is rewritten. Here
it is rewritten with `gamma_v`, because Bernoulli percolation is invariant
under automorphisms. This gives

```text
tau^(n)(o,x) <= 1_S(x) + sum_v nu(v) tau^(n-1)(v,x),
tau^(n-1)(v,x) = tau^(n-1)(o, gamma_v^(-1) x)       (gamma_v is an automorphism).
```

Iterating `n` times (`tau^(0)(o,x) = 1[x = o] <= 1_S(x)`) gives
`tau^(n)(o,x) <= sum_(k<=n) sum_(v_1..v_k) nu(v_1)...nu(v_k) 1_S(gamma_(v_k)^(-1) ... gamma_(v_1)^(-1) x)`.
Sum over `x in L`. For fixed `v_1..v_k`, the substitution
`y = gamma_(v_k)^(-1) ... gamma_(v_1)^(-1) x` is a bijection, and the
cocycle turns `x in L` into `h(v_1)...h(v_k) h(y) = 1`. So
`sum_(x in L) tau^(n)(o,x) <= sum_(k<=n) (mu^{*k} * a)(1)`. Monotone
convergence in `n` gives `sum_(x in L) tau_p(o,x) <= D_p(S)`.

*Upper end.* If `D_p(S) < infinity`, then `E_p|K_o ∩ L| < infinity`, and the
fourth bullet of Part 4 of the level-set proof applies verbatim: a.s. every
cluster meets every level set finitely. So `p <= p_c(L;G)`, and
`p^G(L) <= p_c(L;G)`. The inequalities `p^(l2)(L) = p_T <= p_c(G)` are item 3 of
the level-set node, and `p_c(G) < p_t` is the imported theorem.

*Laplace bound.* For real `lambda` and `f >= 0` on `Lambda` put
`Lf(lambda) = sum_t f(t) t^lambda`. Then `L(f * g) = Lf Lg`, and
`(mu^{*k} * a)(1) <= L(mu^{*k} * a)(lambda) = Lmu(lambda)^k La(lambda)`. So

```text
D_p(S) <= La(lambda) / (1 - Lmu(lambda))      whenever Lmu(lambda) < 1,
```

and `La(lambda) < infinity` because `a` is finitely supported.

*Lower end, `p^G(L) >= p_t`.* Let `d` be the degree. For adjacent `u, v`,
`Stab_v u` is contained in the neighbours of `v`, so `Delta(u,v) <= d`, and by
symmetry `Delta(u,v) >= 1/d`. Take `S = B_R`. Every boundary edge `{u,v}` has
`u in S_R = {d(o,u) = R}`, and `P_p(o <->_S u) <= tau_p(o,u)`. With
`h(v) = h(u) Delta(u,v)`,

```text
Lmu_{B_R,p}(lambda) <= p sum_(u in S_R) tau_p(o,u) sum_(v ~ u) h(v)^lambda
                    <= p d^(1+|lambda|) sum_(u in S_R) tau_p(o,u) Delta(o,u)^lambda.
```

The last sum is the `S_R`-part of `chi_(p,lambda) = sum_u tau_p(o,u) Delta(o,u)^lambda`.
Let `p < p_t`, and choose `lambda` with `chi_(p,lambda) < infinity` (definition
of `p_t`). The sphere parts of a convergent series tend to `0`, so
`Lmu_{B_R,p}(lambda) < 1` for large `R`, and the Laplace bound gives
`D_p(B_R) < infinity`. Hence `p <= p^G(L)`, and `p^G(L) >= p_t`. This proves
the chain of item 8.

*Trees.* Take `T_k`, `xi`, `Gamma = Aut(T_k)_xi` and heights as in Part 5 of
the level-set proof, where `Delta(o,y) = (k-1)^(h(y)-h(o))` and `L` is the
horocycle. Let `S = B_R` and `n = R+1`. In a tree, `o <->_(B_R) u` holds iff
the geodesic is open, so `P_p(o <->_(B_R) u) = p^R` on `S_R`. Each
`v in S_n` has exactly one neighbour in `B_R`. So `nu(v) = p^n` on `S_n`,
and `mu` is `p^n` times the height distribution of `S_n`. By the counting in
Part 5 (with `a + b = n`), `S_n` has
- `1` vertex at height `+n`,
- `(k-1)^n` at height `-n`,
- `(k-2)(k-1)^(b-1)` at height `n - 2b` for `1 <= b <= n-1`.

The total is `k(k-1)^(n-1)`, so the mass is `p^(R+1) k (k-1)^R`. At the half
tilt `lambda = 1/2` (`t^(1/2) = (k-1)^(height/2)`, that is,
`e^(lambda' height)` with `lambda' = (1/2) log(k-1)` as in the target),
`Lmu` has the terms `p^n (k-1)^(n/2)` from each of the two extreme heights and
`p^n (k-2)(k-1)^(b-1) (k-1)^(n/2 - b) = p^n (k-1)^(n/2) (k-2)/(k-1)` for
each of the `n-1` middle values of `b`. Summing,

```text
Lmu_{B_R,p}(1/2) = (p sqrt(k-1))^(R+1) (2 + R (k-2)/(k-1)) = Phi_R(p).
```

For `p < 1/sqrt(k-1)` this tends to `0`, so `p^G(L) >= 1/sqrt(k-1)` without
the import. Part 5 gives `p_c(L;T_k) = p_t = 1/sqrt(k-1)` and
`p^(l2)(L) = 1/(k-1)`, and the upper end gives `p^G(L) <= p_c(L;T_k)`. So
`p^G(L) = p_c(L;T_k)` (the analogue of (E-a)), while
`p^(l2)(L) < p^G(L)` (the analogue of (E-b) fails). Since `Lambda = (k-1)^Z`
is amenable, the `l2(Lambda)` norm of `mu` is its mass. That mass is `>= 1`
for large `R` when `p > 1/(k-1)`, so no ball has an l2 certificate on the
window. The scripts evaluate `Phi_R`, the Chernoff infimum over `lambda`, and
partial sums of `D_p(B_R)` by direct convolution. For `k = 3, 4, 6`, they
find the first certifying radius across the window: for `k = 3` it is
`R = 6, 13, 40, 144, 657` at the fractions `.25, .5, .75, .9, .97` of the way
from `p_c` to `p_t`, with none up to `R = 800` at `p_t`. The log mass is
positive at every certificate. ∎
