---
rg: 2
id: fpbs-kazhdan-uniform-walk-decorrelation-proof
kind: route
title: Kazhdan gap in the cluster Koopman representation, whose invariant vectors are computed by indistinguishability
target: fpbs-kazhdan-uniform-walk-decorrelation
requires:
  - fpbs-bernoulli-cluster-indistinguishability
  - fpbs-cluster-count-trichotomy
---

Notation as in the target. Fix `p`. The cases `p in {0,1}` are covered by
Step 2(b) (at `p=0`, all clusters are finite) and by `a^L_n(1)=1=theta(1)^2`.
So assume `0<p<1` where needed. Write `P = P_p`.

### Step 1. The cluster representation

Fix an enumeration of `Gamma`. Let
`Y = {(omega,x) in Omega x Gamma : x is the first vertex of K_x(omega)}`, where
`K_x(omega)` is the cluster of `x`. Identify `(omega,x)` with the pair
`(omega,K)`, `K = K_x(omega)`; every cluster, finite or infinite, has a first
vertex. Let `m` be the restriction of `P x counting` to `Y`, so that

```text
m(E) = E[ #{clusters K of omega : (omega,K) in E} ].
```

`Gamma` acts on `Y` by `g(omega,K) = (g omega, gK)`. Since `K -> gK` is a
bijection from the clusters of `omega` to those of `g omega`, and `P` is
`Gamma`-invariant, `m(g^(-1)E) = m(E)`. Hence
`(pi(g)F)(omega,K) = F(g^(-1)omega, g^(-1)K)` is a unitary representation on
`H = L2(Y,m)`.

For `x in Gamma` let `xi_x(omega,K) = 1{x in K}`. Then:

* `||xi_x||^2 = m(x in K) = 1`, since exactly one cluster contains `x`;
* `<xi_x, xi_y> = E #{K : x,y in K} = P(x <-> y)`;
* `pi(g) xi_x = xi_(gx)`, since `x in g^(-1)K` iff `gx in K`.

With `mu_L = (delta_e + mu_S)/2` and `pi(nu) = sum_g nu(g) pi(g)`, we get
`pi(mu_L)^n = pi(mu_L^(*n))` and

```text
<pi(mu_L)^n xi_o, xi_o> = sum_g mu_L^(*n)(g) P(o <-> g) = a^L_n(p).      (1)
```

The walk is `X^L_n = s_1 ... s_n` with i.i.d. steps of law `mu_L`, so
`X^L_n` has law `mu_L^(*n)`.

### Step 2. Invariant vectors

**Lemma.** `H^Gamma = C 1_(Y_inf)` if `U_p` holds, and `H^Gamma = 0` otherwise.
Here `Y_inf = {(omega,K) : K infinite}`.

Let `F in H^Gamma`. Each `pi(g)F = F` a.e. and `Gamma` is countable, so after
changing `F` on a null set, `F` is invariant everywhere. For `t>0` the set
`E_t = {|F| > t}` is `Gamma`-invariant and `m(E_t) <= ||F||^2/t^2 < infinity`.

**(a) Finite clusters.** Let `W(omega)` be the union of the finite clusters `K`
with `(omega,K) in E_t`. By Tonelli,

```text
m(E_t ∩ Y_fin) = E[ sum_(x in Gamma) 1{x in W(omega)} / |K_x(omega)| ]
               = sum_x E[ 1{x in W(omega)} / |K_x(omega)| ].
```

Invariance of `E_t` gives `x in W(omega)` iff `o in W(x^(-1)omega)`, and
`|K_x(omega)| = |K_o(x^(-1)omega)|`. So by invariance of `P` every summand
equals `c = E[1{o in W}/|K_o|]`. Finiteness forces `c = 0`, so `o notin W`
a.s. By invariance `W = empty` a.s., and `m(E_t ∩ Y_fin) = 0`.

**(b) No infinite cluster** (`N_inf = 0`, which includes `p = 0`). Then
`Y_inf` is `m`-null. By (a), `F = 0` a.e.

**(c) Infinitely many infinite clusters.** Let
`A = {(V(K), omega) : (omega,K) in E_t, K a cluster of omega}`. It is
measurable and diagonally invariant. By
`fpbs-bernoulli-cluster-indistinguishability`, a.s. either every infinite
cluster lies in `A` or none does. On the first event the count
`#{K infinite : (omega,K) in E_t}` is infinite. Since
`m(E_t ∩ Y_inf) < infinity`, that event is null, and so
`m(E_t ∩ Y_inf) = 0`. With (a), `F = 0` a.e.

**(d) Unique infinite cluster.** The map `omega -> (omega, K_inf(omega))` is a
`Gamma`-equivariant measurable bijection from a full-measure set of `Omega`
onto `Y_inf`, and it carries `P` to `m|Y_inf`. So `F|Y_inf` corresponds to a
`Gamma`-invariant function of `omega`. That function is a.s. constant, since
Bernoulli product measure is mixing, hence ergodic, under the infinite group
`Gamma`. With (a), `F = c 1_(Y_inf)`. Conversely `1_(Y_inf)` is invariant, and
`||1_(Y_inf)||^2 = E[N_inf] = 1`.

By `fpbs-cluster-count-trichotomy`, `N_inf in {0,1,infinity}` a.s. is
constant, so (b)-(d) exhaust the cases.

**Projection of `xi_o`.** Let `Q` be the orthogonal projection onto
`H^Gamma`. Under `U_p`,
`Q xi_o = <xi_o, 1_(Y_inf)> 1_(Y_inf) = m(o in K, K infinite) 1_(Y_inf) = theta(p) 1_(Y_inf)`,
so `||Q xi_o||^2 = theta(p)^2`. Otherwise `Q xi_o = 0`. In both cases
`||Q xi_o||^2 = theta(p)^2 1{U_p}`.

### Step 3. The Kazhdan gap, uniform in p

`H_0 = (H^Gamma)^perp` is `pi`-invariant, and `pi|H_0` has no nonzero
invariant vector. So for unit `v in H_0` some `s in S` has
`||pi(s)v - v|| >= kappa`. Since `S` is symmetric, `pi(mu_S)` is self-adjoint,
and `Re<pi(s)v,v> = 1 - ||pi(s)v-v||^2/2`. Hence

```text
<pi(mu_S)v, v> = 1 - (1/(2|S|)) sum_(s in S) ||pi(s)v - v||^2 <= 1 - kappa^2/(2|S|).
```

So the spectrum of `pi(mu_S)|H_0` lies in `[-1, 1-kappa^2/(2|S|)]`. The
spectrum of `pi(mu_L)|H_0 = (I + pi(mu_S))/2` lies in `[0, eta]`. By the
spectral theorem, `0 <= <pi(mu_L)^n v, v> <= eta^n ||v||^2` for `v in H_0`.

The constant `kappa` depends only on `(Gamma,S)`, not on the representation.
So `eta` is the same for every `p`.

### Step 4. Proof of the Theorem

Write `xi_o = Q xi_o + v` with `v in H_0`. `Q xi_o` is fixed by
`pi(mu_L)`, and `H^Gamma`, `H_0` are orthogonal invariant subspaces, so by (1)

```text
a^L_n(p) = ||Q xi_o||^2 + <pi(mu_L)^n v, v>,
||v||^2 = 1 - ||Q xi_o||^2.
```

Step 2 gives `||Q xi_o||^2 = theta(p)^2 1{U_p}`, and Step 3 gives
`0 <= <pi(mu_L)^n v,v> <= eta^n ||v||^2`. This is the Theorem.

### Step 5. Corollaries

**(1)** Sum the upper bound over `n`.

**(2)** Each `tau_p(o,g) = sup_R P_p(o <-> g inside B_R)` is a nondecreasing
supremum of polynomials in `p`, so it is lower semicontinuous and
nondecreasing. So is `a^L_n(p)`, a finite combination with nonnegative
coefficients. A nondecreasing lower semicontinuous function is
left-continuous. We have `p_u >= p_c > 0`, and no `p < p_u` has uniqueness.
So the Theorem gives `a^L_n(p) <= eta^n` for `p < p_u`, and letting `p`
increase to `p_u` gives `a^L_n(p_u) <= eta^n`. If `U_(p_u)` held, the lower
bound `a^L_n(p_u) >= theta(p_u)^2 > 0` would contradict `eta^n -> 0`. The same
argument at `p_u = 1` would give `1 = a^L_n(1) <= eta^n`, so `p_u < 1`.

**(3)** By (2) and the Theorem, `a^L_n(p) <= eta^n` for `p <= p_u`. So
`lambda_L(p) <= eta` and `A_L(p) <= 1/(1-eta)`.

For the simple walk, `A_L = sum_k a_k sum_n binom(n,k) 2^(-n) = 2A`, so
`A(p) <= 1/(2(1-eta)) = 2|S|/kappa^2`.

For `lambda` with `p > 0`, condition on the walk and apply Harris--FKG to the
increasing events `{o <-> X_k}` and `{edge X_k X_(k+1) open}`. This gives
`a_(k+1) >= p a_k`, so `a_k >= p^(k-n) a_n` for `k >= n`. Then

```text
a^L_(2n) = E[a_(Bin(2n,1/2))] >= P(Bin(2n,1/2) in [n, n+sqrt n]) p^(sqrt n) a_n >= c p^(sqrt n) a_n
```

for a universal `c > 0` and all large `n`. Hence
`a_n <= c^(-1) p^(-sqrt n) eta^(2n)` and `lambda(p) <= eta^2`.

For `p > p_u`, `fpbs-cluster-count-trichotomy` gives uniqueness. So
`theta(p) > 0`, `a_n, a^L_n >= theta(p)^2`, `A = infinity` and
`lambda = lambda_L = 1`.

**(4)** `A(p) < infinity` for some `p > p_c` gives `p_c < p_u` by (3). Next,
`lambda(p) < 1` gives `A(p) < infinity`. Conversely, if `p_c < p_u`, then any
`p in (p_c, p_u)` has `lambda(p) <= eta^2 < 1` and `A(p) < infinity` by (3).

**(5)** This is (3), together with the Theorem applied at `p > p_c = p_u`.

### Consistency checks and provenance

* At `p = 0` the Theorem says `mu_L^(*n)(e) <= eta^n`, the Kazhdan bound for
  the regular representation. It is consistent with `rho_L <= eta`.
* Lyons--Schramm, arXiv:math/9811170, corollary with source label `c.kazhdan`,
  read from the TeX source on 2026-09-17: "If $G$ is a Cayley graph of an
  infinite Kazhdan group $\Gamma$, then $p_u(G) < 1$. Moreover,
  $\P[\exists\hbox{ a unique infinite cluster}]=0$ in Bernoulli($p_u$)
  percolation." Their proof goes through Glasner--Weiss and is not
  quantitative. Their remark `r.alt-proof` mentions a route through
  positive-definite functions. Corollary (2) is a quantitative version of
  that corollary. The p-uniform bound and Corollaries (1) and (3)-(5) are not
  stated there. Nothing in this route uses their corollary.
