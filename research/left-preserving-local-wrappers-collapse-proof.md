---
rg: 2
id: left-preserving-local-wrappers-collapse-proof
kind: route
title: Local completeness makes each 2-to-1 constraint absorb the agreement subgroup, a size count forces translation or merge type, and pair-uniformity leaves translations at most alpha_k of the mass
target: left-preserving-local-richness-wrappers-are-affine-ug-merges
requires: []
artifacts:
  - experiments/rich-2to1-local-wrappers-2026-09-17/check_wrappers.py
---

Notation is as in the target claim. Normalize the edge weights to total 1. Let
`w_z = sum_u w_(uz)` and `w_u = sum_z w_(uz)`.

**(1) Agreement subgroup.** By (LC) the label `c` is a function of `f`. Call it
`g(f)`. Then

```text
g = h_(uz) o r_(uz)     for every u in S_z.
```

Fibres of `r_(uz)` are cosets of `ker dr_(uz)`, so `g(f+v) = g(f)` for
`v in ker dr_(uz)`. Iterating over sums gives `g(f+v) = g(f)` for every
`v in B_z`.

Now take `x in Sigma_u` and `d = dr_(uz)(v)` with `v in B_z`. Pick `f` with
`r_(uz) f = x`, which exists because `r_(uz)` is onto. Then

```text
h_(uz)(x + d) = h_(uz)(r_(uz)(f + v)) = g(f + v) = g(f) = h_(uz)(x).
```

So `h_(uz)` is constant on the cosets of the subgroup `D_u = dr_(uz)(B_z)`. The
fibres of `h_(uz)` have exactly 2 points, so `|D_u| <= 2`, which means `|D_u|`
is 1 or 2.

**(2) Dichotomy.** Since `ker dr_(uz) <= B_z`, we have
`|D_u| = |B_z| / |ker dr_(uz)|`. Every `r_(uz)` is onto a `2k`-point space, so
`|ker dr_(uz)| = |A_z| / 2k` for every `u`. Hence the ratio `|D_u|` is the same
for all `u in S_z`, and the two types exclude each other.

* **Ratio 1.** Each `ker dr_(uz)` is contained in `B_z` and has the same size, so
  each equals `B_z`. Then `r_(uz)` induces an affine bijection
  `psi_u : A_z / B_z -> Sigma_u`. Put `phi_(u'u) = psi_u o psi_(u')^(-1)`. Then
  `r_(uz) = phi_(u'u) o r_(u'z)`, and
  ```text
  h_(u'z)(r_(u'z) f) = g(f) = h_(uz)(phi_(u'u)(r_(u'z) f)).
  ```
  Since `r_(u'z)` is onto, `h_(u'z) = h_(uz) o phi_(u'u)`. This is type (D).
* **Ratio 2.** `D_u = {0, b_u}`, and `h_(uz)` is constant on each
  `{x, x + b_u}`. Both sets have 2 points, so the fibres are exactly these pairs.
  This is type (A).

**(3) Mass bound.** Fix `u` and distinct `x_0, x_1 in Sigma_u`. The pairings
realized at type-(A) edges are translation pairings `tau_b`, `b != 0`, and these
are distinct pairings. Also `tau_b` is contained in the event

```text
E_b = { {x_0, x_0+b} and {x_1, x_1+b} are both blocks }.
```

* If `b = x_0 + x_1`, then `E_b` is the event that `{x_0, x_1}` is a block. Its
  probability is `1/(2k-1)`.
* Otherwise, `x_1` is not in `{x_0, x_0+b}`, and `x_1 + b` is not in that set
  either: the first case would force `b = x_0 + x_1`, the second `x_1 = x_0`. So
  `E_b` asks for two disjoint pairs, and by (R2) its probability is
  `1/((2k-1)(2k-3))`.

There are `2k-2` values of the second kind, so

```text
P_u[type A] <= 1/(2k-1) + (2k-2)/((2k-1)(2k-3)) = (4k-5)/((2k-1)(2k-3)) = alpha_k.
```

The edge mass at type (A) is `sum_u w_u P_u[type A] <= alpha_k`. Under the
uniform law on all `(2k-1)!!` pairings the exact probability is
`(2k-1)/(2k-1)!!`.

If (R2) holds only on left mass `1 - gamma`, the same sum is at most
`gamma + alpha_k`.

**(4) Value floor.** Fix `L` and a type-(D) vertex `z`. Take any `u_0 in S_z` and
put `c = h_(u_0 z)(L_(u_0))`. For every `u` with `L_u = phi_(u_0 u)(L_(u_0))`,

```text
h_(uz)(L_u) = h_(uz)(phi_(u_0 u)(L_(u_0))) = h_(u_0 z)(L_(u_0)) = c.
```

So some choice of `c` satisfies weight at least
`w_z sum_u nu_z(u) [L_u = phi_(u_0 u)(L_(u_0))]`. The best `c` does at least as
well as the average over `u_0 ~ nu_z`, which gives weight at least
`w_z p_z(L)` with `p_z(L) = P_(u_0,u ~ nu_z)[L_u = phi_(u_0 u) L_(u_0)]`.
Type-(A) vertices contribute at least 0. Summing,

```text
val_W(L) >= sum_(z in D) w_z p_z(L) = w(D) val_(U_W)(L) >= (1 - alpha_k) val_(U_W)(L).
```

Maximizing over `L` gives the claimed inequality.

**(5) Certificate completeness.** Let `z` be certified by `f`.

* By (LC), `c = g(f)` satisfies every edge at `z`, so `val_W(L) >= 1 - beta`.
* If moreover `z` is type (D), then
  `L_u = r_(uz) f = phi_(u_0 u)(r_(u_0 z) f) = phi_(u_0 u)(L_(u_0))` for all
  `u_0, u`, so `p_z(L) = 1`.

Hence `val_(U_W)(L) >= (w(D) - beta)/w(D) >= 1 - beta/(1 - alpha_k)`.

**(6) Collapse.**

* *YES case.* The wrapper's completeness proof supplies `L` with uncertified mass
  at most `beta`, so `val(U_W(G)) >= 1 - beta/(1 - alpha_k)` by (5).
* *NO case.* If `val(W(G)) <= s`, then `val(U_W(G)) <= s/(1 - alpha_k)` by (4).

The descriptions of `A_z` and `r_(uz)` are part of the wrapper's output. Kernels,
`B_z`, the types, `phi` and the weights of `U_W` then follow by Gaussian
elimination over `F_2`, in polynomial time. `QED`

**Computation.** The artifact checks the three steps by brute force.

* *Part 1.* 356 random affine sources, with `A = F_2^n` for `n <= 5`, alphabets
  of size 4 or 8, and `|S_z| <= 3`.
  * Agreement classes are computed by union-find on points, not by linear
    algebra, and they coincide with the cosets of `B_z`.
  * All locally complete 2-to-1 labelings are enumerated through the pairings
    of one alphabet: 9153 of type (D) and 67 of type (A), with no mixed case.
  * Survivors exist iff `|B_z| <= 2|ker|`.
* *Part 2.* The exact pairing probabilities for `2k = 4` and `2k = 8` confirm
  both events of (3). The translation mass is `1/15 <= alpha_4 = 11/35`.
* *Part 3.* 60 random mixed wrappers on 4 left vertices. For every one of the
  256 labelings it verifies `val_W(L) >= w(D) val_(U_W)(L)` and both bounds of
  (5). The minimum slack is 0, so (4) is tight.
