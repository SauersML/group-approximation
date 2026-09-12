---
rg: 2
id: fpbs-tree-projected-branch-share-last-crossing-proof
kind: route
title: Decompose at the last entry into each nested branch and apply BK
target: fpbs-tree-projected-branch-share-last-crossing-bound
requires: []
---

Notation as in the target. Put `q_0 = 1` and `q_j = s_1 ... s_j`.

**Cut structure.** Every generator projects to `1` or to a letter, and `F_n` is
a tree. So an edge of `X` joins two vertices of one fibre, or joins
`Gamma_q` to `Gamma_(qs)` for a letter `s`. Hence the only edges between
`pi^(-1) beta(q_j)` and its complement join `Gamma_(q_(j-1))` to `Gamma_(q_j)`.
From a fixed `u in Gamma_(q_(j-1))` there are exactly `m_(s_j)` of them.

**Item 1.** Fix `y in pi^(-1) beta(q_D)` and an open simple path from `o` to
`y`. For `j = 1..D`, let `e_j = (u_j,v_j)` be the last edge of the path entering
`pi^(-1) beta(q_j)`, with `u_j in Gamma_(q_(j-1))` and `v_j in Gamma_(q_j)`.
After `e_j` the path stays in `pi^(-1) beta(q_j)`. Since
`beta(q_(j+1)) ⊆ beta(q_j)` and `u_(j+1) in Gamma_(q_j) ⊆ pi^(-1) beta(q_j)`,
`e_j` precedes `e_(j+1)`. The path therefore splits into edge-disjoint pieces:
* `gamma_0`, from `o` to `u_1`;
* `e_1`;
* `gamma_1`, from `v_1` to `u_2` inside `pi^(-1) beta(q_1)`;
* ...;
* `e_D`;
* `gamma_D`, from `v_D` to `y` inside `pi^(-1) beta(q_D)`.

So `{o <-> y}` is contained in the countable union, over the choices of
`(u_j, e_j)`, of the disjoint occurrence of these increasing events:
* `{o <-> u_1}`;
* `{e_1 open}`;
* `{v_1 <-> u_2 in pi^(-1) beta(q_1)}`;
* ...;
* `{v_D <-> y in pi^(-1) beta(q_D)}`.

The van den Berg–Kesten inequality and a union bound give

```text
tau_p(o,y) <= sum  tau_p(o,u_1) p tau^(beta(q_1))_p(v_1,u_2) p ... p tau^(beta(q_D))_p(v_D,y).
```

Sum over `y`, then `u_D, ..., u_1`, and the edges.
* `sum_y tau^(beta(q_D))_p(v_D,y) <= chi_p`.
* **Translation.** Left multiplication by `v_j^(-1)` is a graph automorphism.
  It maps `Gamma_(q_j)` onto `Gamma_1`, and `pi^(-1) beta(q_j)` onto
  `pi^(-1)(q_j^(-1) beta(q_j)) = pi^(-1)(F_n \ beta(s_j^(-1)))`. So
  `sum_(u in Gamma_(q_j)) tau^(beta(q_j))_p(v_j,u) = chi^(s_j)_p`.
* `sum_(u_1 in Gamma_1) tau_p(o,u_1) = chi^H_p`.
* Each `e_j` contributes `p m_(s_j)`.

Collecting the factors,
`E|K_o ∩ pi^(-1) beta(w)| <= chi^H_p (prod_(j<=D) p m_(s_j)) (prod_(j<D) chi^(s_j)_p) chi_p`,
which is item 1.

**Item 2.**
* *First inequality.* Run the same argument with `D = 1`, summing `y` only over
  `Gamma_s`. By the translation above, the last piece sums to at most
  `chi^(s)_p`, so `sigma_p(s) <= chi^H_p p m_s chi^(s)_p`.
* *Second inequality.* `X^(s^(-1))` lies in `pi^(-1)(F_n \ beta(s))`, so it
  contains no edge into `Gamma_s`. For `v in Gamma_s` and each edge `e = (u,v)`
  with `u in Gamma_1`, the events `{o <-> u in X^(s^(-1))}` and `{e open}` depend
  on disjoint edge sets. So
  `P(v in K_o) >= max_e p tau^(X^(s^(-1)))_p(o,u)`.
* A fixed `v` has at most `m_s` such edges. Therefore
  `sigma_p(s) >= (1/m_s) sum_v sum_e p tau^(X^(s^(-1)))_p(o,u) = p chi^(s^(-1))_p`,
  so `lambda_p(s^(-1)) <= m_s sigma_p(s)`.
* *The bound on `chi^H_p` quoted in the target.* By FKG,
  `P(v in K_o) >= max_e p tau_p(o,u)`. The same averaging gives
  `sigma_p(s) >= p chi^H_p`.

**Item 4.**
* *Fibre sums.* Run the decomposition of item 1 with `y` summed over
  `Gamma_(q_D)` only. The last piece lies in `pi^(-1) beta(q_D)` and starts at
  `v_D in Gamma_(q_D)`, so by the translation above it sums to at most
  `chi^(s_D)_p`. Therefore
  `sigma_p(w) <= chi^H_p prod_(j<=D) p m_(s_j) chi^(s_j)_p = chi^H_p prod_(j<=D) lambda_p(s_j)`.
* *Sphere bubbles.* Square and sum over reduced words `w` of length `R`. These
  are exactly the letter sequences `s_1 ... s_R` with `s_(j+1) != s_j^(-1)`.
  The sum of `prod_j lambda_p(s_j)^2` over them is `1^T N_p^(R-1) v_p`.
* *At `p_c`.* The quantities `tau^(Y)_p(x,y)` are nondecreasing and
  left-continuous in `p`, as suprema of finite-volume connection probabilities.
  So every sum above passes to the left limit at `p_c`, possibly as the value
  `infinity`.

**Item 3.** Let `Phi : F_n -> H^d` be a rough similarity onto a coarsely dense
subset of a closed convex set. Let `a in F_n`, and let `H` be a halfspace with
`d(Phi(a),H) >= D`.
* In `H^d`, every geodesic from `Phi(a)` to a point of `H` passes within a
  universal constant of the nearest-point projection `z` of `Phi(a)` onto `H`.
  The right-angled triangle `(Phi(a), z, x)` is uniformly thin.
* By the Morse lemma, the tree geodesic from `a` to any `q in Phi^(-1)(H)`
  passes within some `R` of a vertex `r_0` with `Phi(r_0)` near `z`, and
  `d(a,r_0) >= D/L - C`. Here `R`, `L`, `C` depend only on `Phi`.
* Hence `Phi^(-1)(H)` is contained in the union of the at most `N_R = |B(r_0,R)|`
  branches `beta` rooted at tree vertices on those geodesics within `R` of
  `r_0`. Each root has depth at least `D/L - C - R` from `a`.

Translate `a` to `1` by an element of `Gamma`.
* By item 1, with `c = sup_(p<p_c) chi^H_p`, `M = max_s m_s` and
  `lambda = sup_(p<p_c) max_s lambda_p(s) < 1`, each such branch share is at
  most `c p M lambda^(D/L - C - R - 1)`.
* The share of `H` is at most `N_R` times this. It tends to zero uniformly in
  `p < p_c`, `a` and `H`. QED.
