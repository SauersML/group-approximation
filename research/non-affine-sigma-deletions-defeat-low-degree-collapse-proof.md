---
rg: 2
id: non-affine-sigma-deletions-defeat-low-degree-collapse-proof
kind: route
title: A swap of two labels per edge kills the zero labelling on every edge while honest labels lose only a 2^(1-k) fraction, and equal kernels round every other triple to a coarsening edge with a deleted label set
target: non-affine-sigma-deletions-defeat-low-degree-collapse
requires: []
artifacts:
  - experiments/non-affine-sigma-deletions-2026-09-17/check_deletion_collapse.py
  - experiments/non-affine-sigma-deletions-2026-09-17/output.txt
---

The notation is that of the target claim and of
`linear-view-unique-verifiers-collapse-proof`. For a triple `t = (w, w', sigma)`
on `e = (a,b)`, put `f(h) = rho_w(h_w)` and `g(h) = rho_(w')(h_(w'))` for
`h in H_e`, and let `K_f, K_g <= L(H_e)` be the kernels of their linear parts on
the direction space of `H_e`. Every `H_e` projects onto both `A_a` and `A_b`.

## Part A (the counterexample)

**Model data.** `A_z = F_2^k` for every vertex `z`. `H_e = { (x, M_e x) }`
projects bijectively onto both coordinates because `M_e` is invertible. There is
one output vertex per outer vertex, with view `rho_z = id`, of degree `1`. Both
triples are cross triples.

**Completeness.** Honest labels on `e` are `x_a` uniform in `F_2^k` and
`x_b = M_e x_a`.

* The triple `sigma_e = M_e` accepts every `h`, so it is exact.
* `sigma'_e(x_a) = M_e(swap(x_a))` equals `M_e x_a` iff `swap(x_a) = x_a`, that is,
  iff `x_a notin {0, u_e}`. So `a_t = 1 - 2/K = 1 - 2^(1-k)`, and the triple is not exact.

So `V_pert` has completeness `1 - 2^(1-k)` and `w_ex = 0`. `V_mix` has
completeness `(1 + 1 - 2^(1-k))/2 = 1 - 2^(-k)` and `w_ex = 1/2`. Both triples
have `K_f = K_g = 0`, so both are roundable with `beta_t = M_e`. The deletion set is
`D_t = F_2^k` for `sigma_e` and `D_t = F_2^k \ {0, u_e}` for `sigma'_e`.
`Can_part(Phi, V_mix)` has vertices `(z, {points})`, labels `F_2^k`, and edge
constraints `M_e` (the exact triples). So it is `Phi` read as a unique game. It is
the same as `Can_rd(Phi, V_pert)`. The labelling `x = 0` satisfies every
constraint, so both have value `1`.

**One edge, one fixed labelling.** Fix `x in (F_2^k)^n` and an edge `e = (a,b)`.
Write `q = 1/(K-1)`.

*(i)* `Pr[sigma'_e(x_a) = x_b] <= q`.

* If `x_a = 0`, then `sigma'_e(0) = M_e u_e`. For fixed `M_e`, the vector
  `M_e u_e` is uniform over nonzero vectors, so the probability is
  `1[x_b != 0] q <= q`.
* If `x_a != 0` and `x_b = 0`, the triple accepts iff `M_e swap(x_a) = 0`, iff
  `swap(x_a) = 0`, iff `u_e = x_a`. That has probability `q`.
* If `x_a != 0` and `x_b != 0`, the triple accepts only if `u_e != x_a`, so that
  `swap(x_a) = x_a`, and `M_e x_a = x_b`. For fixed `x_a != 0`, `M_e x_a` is
  uniform over nonzero vectors and independent of `u_e`. The probability is
  `(1 - q) q <= q`.

*(ii)* `Pr[M_e x_a = x_b] <= q` if `(x_a, x_b) != (0,0)`. If `x_a = 0`, then
`M_e 0 = 0 != x_b`, so the probability is `0`. Otherwise it is at most `q` as above.

*(iii)* On `V_mix` the edge scores `(1/2)(1[M_e x_a = x_b] + 1[sigma'_e(x_a) = x_b])`.

* If `(x_a, x_b) = (0,0)`, the exact triple accepts and the perturbed triple
  rejects, because `M_e u_e != 0`. The score is exactly `1/2`.
* Otherwise the score is at most the indicator `Y_e` of "some triple accepts".
  By (i), (ii) and a union bound, `Pr[Y_e = 1] <= 2q`.

So `val_x(V_mix) <= 1/2 + (1/m) sum_e Y_e`. The script's check "A score table"
tests the pointwise part of (iii) for every `(x_a, x_b)`.

**First moment.** For fixed `x`, the events on distinct edges depend on
independent data `(M_e, u_e)`. So `X = sum_e 1[sigma'_e(x_a) = x_b]` is a sum of
independent indicators, each with mean at most `q`. For an integer `r >= sm`, a
union bound over `r`-subsets of edges gives

```text
Pr[X >= r]  <=  C(m, r) q^r  <=  (e m q / r)^r  <=  (e / (s (K-1)))^r  <=  (e / (s (K-1)))^(s m),
```

where the last step uses `e/(s(K-1)) < 1`. The same bound with `2q` holds for
`sum_e Y_e`. There are `K^n` labellings. So

```text
Pr[ val(V_pert) > s  or  val(V_mix) > 1/2 + s ]  <=  2 K^n (2e / (s (K-1)))^(s m).
```

Take `m >= 3n/s` and `K >= 64 e^3 / s^3`. Then `K - 1 >= K/2`, and
`(s(K-1)/(2e))^3 >= s^3 K^3 / (64 e^3) >= K^2`. Hence
`(2e/(s(K-1)))^(sm) <= (2e/(s(K-1)))^(3n) <= K^(-2n)`, and the probability is at
most `2 K^(-n)`. Nothing about the graph was used, so the bound holds for every
fixed multigraph.

**Refutation.** Fix `gamma in (0,1)` and `s = 1/4`. For every
`k >= max(17, 1/(1-gamma))`, let `K = 2^k >= 64 e^3 4^3 ~ 82,300`, and let
`n = 5`, `m = 12n` on any multigraph. The probability above is positive, so there are
`M_e, u_e` with `val(V_mix(Phi)) <= 3/4`. Here `eps = 2^(-k)`,
`d = 1 <= (1-gamma) k = (1-gamma) log_2(1/eps)`, and `val(Can_part(Phi, V_mix)) = 1`.
The inequality `val(V) >= (1 - o(1)) val(Can_part) - o(1)` would force
`val(V_mix) -> 1` along `k -> infinity`, but `val(V_mix) <= 3/4`. So
`low-degree-view-collapse-survives-non-affine-sigma` is false. The perturbed game
gives the stronger picture: `val(V_pert) <= 1/4` while its rounded coarsening
`Can_rd` has value `1`. Every labelling of `Can_rd` that satisfies more than `1/4`
of the edges must use the deleted labels, here the label `0`.

## Part B (the deletion coarsening)

### Item 1: rounding threshold

**Non-roundable triples.** Lemma 1(b) of `linear-view-unique-verifiers-collapse-proof`
applies to arbitrary bijections `sigma`. It gives
`a_t <= 1/[K_f : K_f cap K_g]` and `a_t <= 1/[K_g : K_f cap K_g]`. If
`K_f != K_g`, one of the indices is at least `p`, so `a_t <= 1/p`.

**Weight bound.** `c = sum_t tau_t a_t <= w_r + (1 - w_r)/p`, which gives
`w_r >= (pc-1)/(p-1)`.

**Deleted mass.**

```text
sum_(t roundable) tau_t (1 - a_t)  =  w_r - c + sum_(t not roundable) tau_t a_t
                                    <= w_r - c + (1 - w_r)/p   <=  1 - c.
```

**`beta_t` for a roundable triple.** Suppose `K_f = K_g`, and let `K = ker rho_w`
and `K' = ker rho_(w')` on `L(A_(o(w)))` and `L(A_(o(w')))`. For `h, h' in H_e`,
`h - h' in K_f` iff `(h - h')_w in K`, and similarly for `K_g`. So
`h_w + K = h'_w + K` iff `h_(w') + K' = h'_(w') + K'`. The relation
`R_t = { (h_w + K, h_(w') + K') : h in H_e }` is therefore the graph of an
injective partial map. Both projections of `H_e` are onto, so it is the graph of a
bijection `beta_t : A_(o(w))/K -> A_(o(w'))/K'`. It is affine because `R_t` is an
affine image of `H_e`, and it depends only on `H_e`, on the coordinates read and on
`K, K'`. In the same-owner case `R_t` is the diagonal, so `K = K'` and `beta_t = id`.

**Deletion density.** `f(h) = rho-bar_w(h_w + K)` and
`g(h) = rho-bar_(w')(h_(w') + K') = rho-bar_(w')(beta_t(h_w + K))`. So `h` is
accepted iff `h_w + K in D_t`. The map `h -> h_w + K` is an affine surjection
`H_e -> A_(o(w))/K`, so its fibres have equal size. Hence
`a_t = |D_t| / |A_(o(w))/K|`. This is check (D) of the script. Check (W) tests the
weight bound and the deleted mass, and check (R) tests `a_t <= 1/2` for
non-roundable triples.

### Item 2: collapse

Let `l` be a labelling of `Can_del` and set `F(w) = rho-bar_w(l(o(w), K_w))`.
Take a roundable `t` that `l` satisfies, meaning `j = l(o(w), K) in D_t` and
`l(o(w'), K') = beta_t j`. Then

```text
sigma(F(w)) = sigma(rho-bar_w(j)) = rho-bar_(w')(beta_t j) = F(w'),
```

where the middle equality is the definition of `D_t`. So `V(Phi)` accepts `t`.
Summing,

```text
acc_V(F)  >=  sum_(t roundable) tau_t 1[l satisfies t in Can_del]  =  w_r val_(Can_del)(l).
```

Maximizing over `l` gives `val(V(Phi)) >= w_r val(Can_del(Phi, V))`. This is check
(T) pointwise and check (M) by brute force. Views with the same owner and kernel
give the same `Can` vertex. Their offsets enter only through `rho-bar_w`, which
the argument uses per triple, so different offsets are harmless. The constraint
`beta_t` of a roundable cross triple is the graph `R_t`, exactly as for exact
triples. So Corollary 5 of `linear-view-unique-verifiers-collapse-proof`, which
uses only that `R_t` is the graph of a bijection, applies verbatim. Every branch of
a 2-to-2 constraint gives the same `beta_t`. The deletion sets `D_t` depend on
`sigma` and the offsets, but not on the branch either, since they are defined from
`beta_t`, `sigma` and the views.

### Item 3: spread lemma

**Equivariance.** Let `s in S` and put `[s]_z = s_z + K` on the vertex `(z, K)`.
For a roundable cross triple on `e`, suppose `(u, u') in R_t` comes from `h`. Then
`h + (s_a, s_b) in H_e`, so `(u + [s_a], u' + [s_b]) in R_t`. That is,
`beta_t(u + [s_a]) = beta_t(u) + [s_b]`. For a same-owner triple, `beta_t = id` and
both endpoints shift by the same `[s_z]`. So `l` satisfies `t` in `Can_rd` iff
`l + [s]` does, and `val_(Can_rd)(l + [s]) = val_(Can_rd)(l)`. This is check (S),
first part.

**Averaging.** `s -> [s_(o(w))]` is a group homomorphism `S -> L(A_(o(w)))/K`
with image `W_t`. So for uniform `s in S`, `[s_(o(w))]` is uniform on `W_t`. Fix
`l`, and let `t` be a roundable triple that `l` satisfies in `Can_rd`, with
`j = l(o(w), K)`. Then `l + [s]` satisfies `t` in `Can_rd` for every `s`, and
it fails `t` in `Can_del` iff `j + [s_(o(w))] notin D_t`. The coset `j + W_t` has
`|W_t|` points and meets the complement of `D_t` in at most
`(1 - a_t)|A_(o(w))/K|` of them. So

```text
Pr_s[ j + [s_(o(w))] notin D_t ]  <=  (1 - a_t) [L(A_(o(w)))/K : W_t].
```

Averaging over the roundable triples with weights `tau_t / w_r`,

```text
E_s val_(Can_del)(l + [s])  >=  val_(Can_rd)(l) - sum_(t roundable) (tau_t / w_r)(1 - a_t)[L(A_(o(w)))/K : W_t].
```

This is check (S), second part. If every index is `1`, item 1 bounds the loss by
`(1-c)/w_r`. Then some `s` has
`val_(Can_del)(l + [s]) >= val_(Can_rd)(l) - (1 - c)/w_r`, and item 2 gives
`val(V(Phi)) >= w_r val(Can_rd(Phi, V)) - (1 - c)`.

### Item 4: the index is needed

In Part A, `S = { s : s_b = M_e s_a for every e }`. Suppose the graph is connected
and its cycle space has dimension at least `2`.

1. Choose a spanning tree `T` and a root `v_0`. Pick two non-tree edges `e_1, e_2`.
2. Along `T`, `s` is determined by `s_(v_0)`: `s_z = T_z s_(v_0)`, where `T_z` is
   the product of the `M_e^(+-1)` on the tree path. The edge `e_i = (a,b)` then
   requires `P_i s_(v_0) = s_(v_0)`, where `P_i = T_b^(-1) M_(e_i) T_a`.
3. Condition on all tree matrices. Then `P_1` and `P_2` are independent and
   uniform in `GL_k(F_2)`, because `M_(e_1)` and `M_(e_2)` are.
4. For fixed `v != 0`, `P_i v` is uniform over nonzero vectors, so
   `Pr[P_i v = v] = q`. Hence

```text
Pr[S != {0}]  <=  sum_(v != 0) Pr[P_1 v = v] Pr[P_2 v = v]  =  (K - 1) q^2  =  1/(K-1).
```

When `S = {0}`, every `W_t = {0}` and every index is `K = 2^k`. The loss term for
`V_pert` is `2^(1-k) 2^k = 2 >= 1`, so the spread bound says nothing. That must
happen, because `val(V_pert) <= s` while `w_r val(Can_rd) - (1 - c) = 1 - 2^(1-k)`.

## Consequence paragraph

The comparison of symmetry spaces in the claim's last paragraph uses two facts.

* **Unfolded Grassmann agreement game.** `H_e` asks two subspaces to agree on
  their intersection, and every global linear functional restricts to a
  homogeneous symmetry. The restriction map onto each view quotient is onto.
* **Folded, over-determined 3LIN inputs.** Here `S` is the solution space of the
  homogeneous system, which is `{0}` for over-determined random instances.

These describe where item 3 does and does not apply. They are not used in Parts A
or B.

## Verification

`nice -n 10 timeout 1200 python3 experiments/non-affine-sigma-deletions-2026-09-17/check_deletion_collapse.py`
(seed `20260917`, `70` trials) writes `output.txt` and exits `0`. It checks:

* **Part A** on four small random instances. It checks `val(Phi) = 1` via the zero
  labelling, the exact completeness `1 - 2^(1-k)`, that `V_pert` rejects the zero
  labelling on every edge, and the score table of (iii). It also reports
  `val(V_pert)` and `val(V_mix)` by exhaustive search.
* **Part B**, checks (R), (W), (D), (T), (S) and (M) on random verifiers with
  affine views over random linear outer games with planted symmetries, and random
  or sparsely perturbed bijections `sigma`.
