---
rg: 2
id: bounded-rank-parity-selectors-representation-weight-proof
kind: route
title: Conditioning on what a bounded-rank parity view reveals leaves the branch bit equal to the parity of the violated equations it combines, so its bias is the weight enumerator of the representation coset, and a second moment over each B-vertex turns that into a bound on the lift value itself
target: bounded-rank-parity-selectors-pay-representation-weight
requires: []
artifacts:
  - experiments/ugc-parity-leak-2026-09-18/check_parity_leak_bias.py
---

Notation is that of the target claim. The proof is self-contained; the only
imported facts are item 3 (the direction law) and item 5 (unfolding at clean
copies) of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`, both
used only in the Corollary and both quoted verbatim there.

## Step 0: the honest lift value is a per-vertex imbalance

Fix `t` and an orientation `o`. The lift `U_o` has right labels `(tau, beta)`
and accepts `(sigma, (tau, beta))` iff `sigma|_(L') = tau` and
`sigma(x_e) xor o_e(tau) = beta`. Give the A-vertices the honest labels. For a
clean constraint `e` at `v` (its window satisfied by `t`) the honest A-label is
`t|_(L_e)` and `p_e(t|_(L_e)) = t|_(L'_v)`, so **every** clean constraint at `v`
projects to the same B-label `tau_hon := t|_(L'_v)`, and it is accepted with the
right label `(tau_hon, beta)` exactly when `beta = A_e`, where
`A_e = <t, x_e> xor o_e(tau_hon)`. Choosing any other `tau` can only pick up
unclean constraints. Hence

```text
hon-lift(o,t)  <=  eps_out + sum_v max_(beta) sum_(e in S, e at v) w_e 1[A_e = beta]
               =   eps_out + sum_v ( w_v(S) + |X_v| ) / 2
               <=  1/2 + eps_out + (1/2) sum_v |X_v|,
```

using `sum_v w_v(S) <= 1` and `max(a, 1-a) = (1 + |2a-1|)/2`.

`A_e` does not depend on the representative `x_e in L_e \ L'`: the two preimages
of `tau` under `p_e` differ at every point of `L_e \ L'` (item 1 of the
membership node), so the accepting bit flips with the representative together
with `<t, x_e>`.

## Step 1: what the observation reveals

Write `U := U_e union U_f` for two constraints at one B-vertex,
`E_U := Span(1_j : j in U)`, `C := C_e + C_f`,
`Lambda := L'_v + Span(m_j : j in U) = L'_v + H_(U_e) + H_(U_f)`, and
`theta := 1 - 2 eta`. Draw `(t, v)` from `Y(M, eta)` and condition on the event

```text
G := { v_j = 0 for all j in U } = { t satisfies the equations of U_e and U_f }
   = { e, f both clean }.
```

Under `G` the restricted noise `v' := v|_([m] \ U)` still has independent
`Bernoulli(eta)` coordinates and is independent of `t`, which is still uniform.
For `c in C`,

```text
<c, b> = <M^T c, t> + <c, v> = <M^T c, t> + <c', v'>,        c' := c|_([m] \ U).
```

Since `E_U <= C`, the observation `O = (t|_(L'), (<c,b>)_(c in C))` determines
`b|_U`, hence under `G` the values `<m_j, t>` for `j in U`, hence the linear form
`t` restricted to all of `Lambda`. Put

```text
K := { c in C : M^T c in Lambda },
```

and fix a complement `C_0` of `K` in `C`.

**(1a)** For `c in K`, `<M^T c, t>` is `O`-measurable, so `O` determines
`<c', v'>`.

**(1b)** The map `c |-> M^T c mod Lambda` is linear on `C` with kernel exactly
`K`, so it is injective on `C_0` and its image is a subspace of `F_2^n / Lambda`
of dimension `dim C_0`. Therefore, conditionally on `t|_(Lambda)`, the vector
`(<M^T c, t>)_(c in C_0)` is uniform on `F_2^(C_0)` and independent of `v'`.

**(1c)** Consequently, for every value `o` of `O`,

```text
P(v' = w | O = o)  proportional to  P(v' = w) * 1[ <c', w> = sigma(c) for all c in K ],
```

where `sigma(c)` is the value of `<c', v'>` read off `o` by (1a): the `C_0` part
of the observation multiplies every `w` by the same factor `2^(-dim C_0)` by
(1b), and the `t|_(Lambda)` part does not involve `v'`. So the posterior law of
`v'` given `O` is its prior conditioned on the linear constraints indexed by
`K'`, where `K' := { c' : c in K } <= F_2^([m] \ U)`.

**(1d)** `s := dim K' <= dim( C / (C meet E_U) ) <= 2R`, because the restriction
map has kernel `C meet E_U`, and
`C meet E_U >= (C_e meet E_(U_e)) + (C_f meet E_(U_f))`.

## Step 2: the blind case

Suppose no `c in C` has `M^T c in x + Lambda`, where `x := x_e + x_f`; that is,
`x notin Lambda + M^T C`. The linear forms of `t` appearing in `O` are
`<t, lambda>` for `lambda in Lambda` and `<M^T c, t>` for `c in C`; they span
`Lambda + M^T C`. Conditionally on `v'`, `t` is uniform, so `<t, x>` is a
uniform bit independent of all of them. Hence

```text
E[ (-1)^(<t,x>) | O, G ] = 0    exactly,
```

for every choice of the functions `Phi_e, Phi_f`. This is item 1 of Theorem 1.
With `C_e` spanned by coordinate vectors and `f` replaced by a fictitious
constraint with `x_f = 0` it is Step 1--2 of
`view-local-branch-selectors-gauge-blindness-proof`, with the uniform planted
`t` in the role of the uniform gauge `z`.

## Step 3: the leaking case

Suppose `c_0 in C` has `M^T c_0 = x + lambda` with `lambda in Lambda`. Then

```text
<t, x> = <M^T c_0, t> + <t, lambda> = <c_0, b> xor <c_0', v'> xor <t, lambda>,
```

and `<c_0, b>`, `<t, lambda>` are `O`-measurable. So

```text
E[ (-1)^(<t,x>) | O, G ] = (+/-) E[ (-1)^(<c_0', v')) | O, G ],
```

with an `O`-measurable sign. **The selector's prediction of the branch bit is
correct exactly when the equations it combines are violated an even number of
times.**

By (1c) the remaining expectation is over the prior of `v'` conditioned on the
values `sigma(k')`, `k' in K'`. Using
`1[ <k', v'> = sigma(k') for all k' ] = 2^(-s) sum_(k' in K') (-1)^(<k',v'> + sigma(k'))`
and `E[(-1)^(<u, v'>)] = theta^(|u|)`,

```text
E[ (-1)^(<c_0', v'>) | sigma ]
      =  ( sum_(k' in K') (-1)^(sigma(k')) theta^(|c_0' + k'|) )
       / ( sum_(k' in K') (-1)^(sigma(k')) theta^(|k'|) ).
```

The numerator is at most `sum_(k') theta^(|c_0' + k'|)` in absolute value. The
set `c_0 + K` is exactly `{ c in C : M^T c in x + Lambda }`, so every element of
`c_0' + K'` has weight at least `W_(ef)` by definition, and the numerator is at
most `2^s theta^(W_(ef))`. The denominator is at least
`1 - sum_(k' != 0) theta^(|k'|) >= 1 - (2^s - 1) theta^(g_(ef))`, by the
definition of `g_(ef)`. Both bounds are monotone in `s`, and `s <= 2R` by (1d),
so whenever `2^(2R) theta^(g_(ef)) <= 1/2`,

```text
| E[ (-1)^(<t,x>) | O, G ] |  <=  2^(2R) theta^(W_(ef)) / (1 - 2^(2R) theta^(g_(ef)))
                              <=  2^(2R+1) theta^(W_(ef)).
```

This is item 2 of Theorem 1. Write `beta_(ef)` for the resulting bound, capped
at 1, and `beta_(ef) = 0` in the blind case.

## Step 4: second moment and Cauchy--Schwarz

The vertices, subspaces, weights and directions of the window family depend only
on `M`, so the weights `w_v, w_e` are deterministic and the expectations over
`v` (the vertex) and over the ensemble commute. Put `Y_v := X_v / w_v` and
`hat w_e := w_e / w_v`. Then `sum_v |X_v| = sum_v w_v |Y_v|`, and by
Cauchy--Schwarz against the probability weights `w_v`, then Jensen over the
ensemble,

```text
E[ sum_v |X_v| ]  <=  E[ ( sum_v w_v Y_v^2 )^(1/2) ]  <=  ( E_v E[ Y_v^2 ] )^(1/2).
```

Expand the inner square:

```text
E[Y_v^2] = sum_(e, f at v) hat w_e hat w_f E[ 1[e, f in S] (-1)^(A_e + A_f) ].
```

*Diagonal.* `e = f` contributes at most `sum_e hat w_e^2 = 1/D_v`.

*Off-diagonal.* For `e != f`,
`A_e + A_f = <t, x_e + x_f> + o_e(tau_hon) + o_f(tau_hon)`, and
`1[e, f in S] = 1_G`. Given `O` and `G`, both `o_e(tau_hon)` and
`o_f(tau_hon)` are determined: they are functions of the measurements, which are
components of `O`, and of `tau_hon = t|_(L')`, which is a component of `O`.
Hence

```text
| E[ 1_G (-1)^(A_e + A_f) ] | = | E[ 1_G (-1)^(o_e + o_f) E[ (-1)^(<t, x_e + x_f>) | O, G ] ] |
                              <= P(G) * beta_(ef)  <=  beta_(ef),
```

and also `<= 1` trivially. Summing,
`E[Y_v^2] <= 1/D_v + sum_(e != f) hat w_e hat w_f min(1, beta_(ef))`, whose
vertex average is `E_v[1/D_v] + Lambda(theta)`. With Step 0,

```text
E[ hon-lift(o, t) ]  <=  1/2 + E[eps_out] + (1/2) sqrt( E_v[1/D_v] + Lambda(theta) ),
```

which is Theorem 2. `E[eps_out] = Pr_U[ t violates an equation of U ] <= k eta`
by a union bound over the `k` equations of a uniformly drawn window. QED

## Step 5: Lemma 3

Let `T` be disjoint from `U_e union U_f`, `1 <= |T| <= N`, with
`sum_(j in T) m_j in x_e + x_f + Lambda_(ef)`. Every element of that coset is
supported inside `P_(ef) = vars(U_e) union vars(U_f)`: indeed
`x_e in X_(U_e)`, `x_f in X_(U_f)`, `H_(U_e) <= X_(U_e)`, `H_(U_f) <= X_(U_f)`,
and `L' <= X_V <= X_(U_e)`. So every variable outside `P_(ef)` has even, hence
at least 2, degree in `T`. Counting incidences,

```text
3|T| = sum_(z in vars(T)) deg_T(z) >= 2( |vars(T)| - |vars(T) meet P| ) + |vars(T) meet P|,
```

so `|vars(T) meet P| >= 2|vars(T)| - 3|T| >= 2(2|T| + 1) - 3|T| = |T| + 2` by
`N`-expansion. But under `P`-isolation every row of `T` has at most one variable
in `P`, so `|vars(T) meet P| <= |T|`. Contradiction; hence `W_(ef) > N`. The
same argument with the coset `Lambda_(ef)` in place of
`x_e + x_f + Lambda_(ef)` gives `g_(ef) > N`. QED

## Step 6: the Corollary's parameters

Fix a B-vertex `v = (V, L')`. For a neighbouring window `U`, the constraints at
`v` with that window are the `L in Gr(X_U, l)` with `L' < L` and
`L meet H_U = 0`, equivalently the cosets `x + L'` with
`x in X_U \ (L' + H_U)`; there are

```text
D = ( 2^(3k) - 2^(l-1+k) ) / 2^(l-1)
```

of them, so `E_v[1/D_v] <= 1/D <= 2^(l-3k+1)`, and by item 3 of the membership
node, quoted verbatim — *"Given `(w_e, a_e) = ((V,L'), U)`, the direction `x_e`
is uniform on `X_U \ (L' + H_U)`"* — the uniform weighting used here is the
instance's own.

*Collapse.* Same window: given `e`, the constraints `f` with
`x_f in x_e + L' + H_U` are the cosets inside `x_e + L' + H_U`, a set of
`2^(l-1+k)` vectors disjoint from `L' + H_U`, so there are `2^k` of them,
including `e`. Different windows: under hypothesis (G),
`(L' + H_(U_e) + H_(U_f)) meet X_(U_e) = L' + H_(U_e)`, so
`(x_f + Lambda_(ef)) meet X_(U_e)` is empty or a coset of `L' + H_(U_e)` and the
count is again at most `2^k`. Hence `kappa <= 2^k / (D - 1) <= 2^(l-2k+1)` for
`k >= 2`.

*Leak.* Where `W_(ef), g_(ef) > W` the bound of Theorem 1 gives
`beta_(ef) <= 2^(2R+1) theta^W`, provided `2^(2R) theta^W <= 1/2`, which holds
for `R <= eta W` and `W` large, since
`log_2(1/theta) >= 2 eta / ln 2 > 2.88 eta`. Adding the weight `rho` of
B-vertices where the hypothesis fails,

```text
Lambda(theta)  <=  kappa + rho + 2^(2R+1) theta^W,
```

and Theorem 2 gives the Corollary. Letting `n -> infinity` (so `W -> infinity`
and `rho -> 0`), then `k -> infinity`, then `eta -> 0` with `k eta -> 0`, the
right-hand side tends to `1/2`. QED

## What the artifact checks

`check_parity_leak_bias.py` verifies Step 2 and Step 3 by exhaustive enumeration
of `(t, v)` at `n = 9`, `m = 10`: for a blind measurement space the conditional
bias is `0` in every observation cell, and for a leaking one it never exceeds
the Step 3 bound. It measures the two geometric parameters of Step 6 (`D` and
`kappa`, the latter agreeing with the imported direction law to five decimals),
counts the short representations of Step 5 on random sparse sources, and
measures the honest lift value of four concrete selectors, two of them the
natural global ones.
