---
rg: 2
id: high-advantage-selector-witnesses-decode-proof
kind: route
title: Markov on the per-vertex failure mass gives a uniform decoding rate at every good target vertex, so the outer loss is multiplicative instead of additive and any outer labelling of value above one half plus the bad mass decodes
target: high-advantage-selector-witnesses-decode-good-outer-labellings
requires:
  - efficient-branch-selectors-list-decode-honest-outer-labels
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
  - orientation-lifts-sandwich-2to1-game-values
artifacts:
  - experiments/ugc-selector-rigidity-2026-09-17/check_high_advantage_decoder.py
---

The notation is that of the target claim and of the parent
`efficient-branch-selectors-list-decode-honest-outer-labels-proof`, whose
Steps 0 and 2 are reused verbatim except for one constant.

## Theorem 3

**Decoder.** Run Step 0 of the parent with `Lambda := { alpha : hat F(alpha) >= 1/8 }`.
Accept iff `val_Phi(hat lambda) >= p0^2 c1 / 2`. It is polynomial time for the
same reasons as in the parent. If `x notin Lang`, every outer labelling has value
`<= s < p0^2 c1 / 2`, so the decoder never accepts.

**Fix the witness.** Let `x in Lang`. Condition on the event, of probability
`>= theta`, that there are `lambda`, `H` and `W` as in the hypothesis:

* `val_Phi(lambda) >= 1 - eps`;
* `H` is honest for `lambda`, with clean set `Cl` and `mu(Cl) >= 1 - d`;
* `W` agrees with `H` outside a constraint set of mass `<= zeta`;
* `val_(G_g)(W) >= 1 - xi`.

`W` and `H` satisfy the same oriented constraints outside the disagreement set.
Hence `val_(G_g)(H) >= 1 - xi - zeta`. Put `h_w := H_w`.

**Step 1': per-vertex failure mass.** For a constraint `e`, let `Ok(e)` be the
event "`e in Cl` and `H` satisfies the oriented `e`". By (B_d), `Ok(e)` implies
`g_e(h_(w_e)) = <lambda_(a_e), x_e>`. Put

```text
delta_a := Pr_(e ~ mu)[ not Ok(e) | a_e = a ].
```

Then `E_(nu_A) delta <= (xi + zeta) + d`. Let `Bad := { a : delta_a > 1/4 }`. By
Markov, `nu_A(Bad) <= 4 (xi + zeta + d)`. By the second half of (M=),

```text
rho_A(Bad) <= 4 K' (xi + zeta + d).                                    (1)
```

**Step 2': a uniform rate at every good vertex.** Fix `a notin Bad`. Define
`beta_(w,a)` as in the parent's Step 1. Then

```text
E_(w ~ nu(.|a)) beta_(w,a) = Pr[ g_e(h_(w_e)) = <lambda_a, x_e> | a_e = a ] - 1/2
                          >= (1 - delta_a) - 1/2 >= 1/4.
```

Let `P_a := Pr_(w ~ nu(.|a))[beta_(w,a) >= 1/8]`. Since `beta <= 1/2`,

```text
1/4 <= P_a (1/2) + (1 - P_a)(1/8),     so     P_a >= 1/3.
```

Fix `w` with `beta := beta_(w,a) >= 1/8`, and suppose the decoder drew `s = h_w`.
This has probability `1/|Sigma_w| >= 2^(-l)`. The computation in the parent's
Step 2 gives, using only (E) and `|F chi| <= 1`,

```text
hat F(lambda_a) >= 2 beta - 2 tau >= 1/4 - 1/8 = 1/8,
```

so `lambda_a in Lambda`. By Parseval `|Lambda| <= 64`. Hence

```text
q_a := Pr[ hat lambda_a = lambda_a ] >= (1/3) 2^(-l) (1/64) = 2^(-l)/192 = p0      for every a notin Bad.   (2)
```

This is the only new point. The parent bounds only the average `E q`, because
at advantage `1/2 + gamma` most vertices can have no advantage. At lift value
`1 - xi`, Markov puts all but `O(xi + zeta + d)` of the target mass at
advantage `>= 1/4`, so the decoding rate is uniform on the good vertices.

**Step 3': multiplicative outer loss.** Draw `(a,b) ~ rho` and `a' ~ rho(.|b)`, as
the decoder does. Then `(a', b)` is also `rho`-distributed. Use the four events
`X, Y, C, D` of the parent's Step 4. On `X, Y, C, D` the decoded edge `(a,b)` is
satisfied. Condition on `(a, b, a')`:

* if `a != a'`, the decoder's coins at `a` and `a'` are independent, so
  `Pr[X and Y] = q_a q_(a')`;
* if `a = a'`, then `X = Y` and `Pr[X and Y] = q_a >= q_a q_(a')`.

`C` and `D` are determined by `(a, b, a')`. Therefore

```text
E val_Phi(hat lambda) >= E[ q_a q_(a') 1{a notin Bad, a' notin Bad, C, D} ]
                     >= p0^2 Pr[ a notin Bad, a' notin Bad, C, D ]           by (2)
                     >= p0^2 ( 1 - 2 rho_A(Bad) - 2 eps )                    union bound
                     >= p0^2 ( 1 - 8 K' (xi + zeta + d) - 2 eps ) = p0^2 c1.  by (1)
```

Here `Pr[not C] = Pr[not D] = 1 - val_Phi(lambda) <= eps`, and `a` and `a'` are
each `rho_A`-distributed. Values lie in `[0,1]`, so
`Pr[val_Phi(hat lambda) >= p0^2 c1/2] >= p0^2 c1/2`. The decoder accepts
`x in Lang` with probability `>= theta p0^2 c1 / 2` and never accepts
`x notin Lang`. Repetition gives `Lang in RP`. `square`

(Part (iii) of the artifact checks both inequalities of this chain exactly on
60 toy instances. Part (ii) checks (2) at every good vertex.)

## Corollary A

Fix `(l, k)` as stated. We apply Theorem 3 to the LEC `(Phi_k, U_(o')(G_multi))`,
where `o'` is the copy of the selector's orientation `o` of `G_folded`.

**The LEC data.** The following are imported from
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`.

* The annotation of the copies is as in that node. So `m = 3k`, and (E) holds
  with `tau = 2^(l-1-2k) <= 1/16` (item 3).
* `nu_A = rho_A` (item 4), so (M=) holds with `K = K' = 1`.
* On NO instances, `val(Phi_k) <= eps_k` (the NO-instances paragraph of
  `dkkms-selector-membership-proof`, from Lemma 5.4).
* Regular `Gap3Lin(1 - eps_3, s*)` is NP-hard (Theorem 4.1, quoted there as
  (Q1)).

The seed alphabet of the doubled lift is `Fun(L') x {0,1}`, of size `2^l`.
Neither (E) nor (M=) depends on the seed alphabet: both concern only the law
of `(w_e, a_e, x_e)`.

**Copying the orientation.** Let `o` be an orientation of `G_folded`, and let
`(C, (V,L'))` be a folded constraint.

* By the quoted definition, the folded constraint accepts `(sigma, sigma')` only
  if every member's multi-edge accepts it, and the weights are summed.
* Each multi-edge is exactly 2-to-1 (item 1). Each fibre of the folded relation
  lies inside a fibre of the multi-edge.
* Put `o'_e := o` on the pairs the folded constraint accepts. On a multi-edge
  fibre that contains only one folded-accepted element `sigma_1`, give the
  other element the opposite bit.

Then `o'` is an orientation of `G_multi`, computable in polynomial time from
`o`. Let `(sigma, (sigma', b))` satisfy the `U_o` edge `(C, (V,L'))`. Then
`(sigma, sigma')` is folded-accepted and `o(sigma) = b`. So every multi-edge of
that aggregate is satisfied in `U_(o')` by the same labels. The multi-edges of
an aggregate carry exactly its weight. Hence, for every labelling `W`,

```text
val_(U_(o')(G_multi))(W) >= val_(U_o(G_folded))(W).                       (3)
```

**(B_d) for patchworks.** Let `H = hon_kappa(lambda, b)`. Let `e` be a clean
copy with member `(U,L)`, and suppose `H` satisfies the `U_(o')` edge `e`. Then
the bijection of `e` sends `H_C` to `H_(V,L') = (lambda_V|_(L'), b)`. By
definition, `G_e(H_(V,L'))` is the value at `x_e` of the unfolding of `H_C` at
`(U,L)`. Cleanness says this unfolding is `lambda_U|_L`. So

```text
G_e(H_(w_e)) = lambda_U(x_e) = <lambda_(a_e), x_e>.
```

So `H` is honest for `lambda` with dirt `d_kappa(lambda)`, for every
orientation.

**The two bullet facts.**

* **Global assignments.** Suppose `lambda = lambda^a`, and `kappa` picks a
  member with clean `U` in every class that has one. Then `hon_kappa(lambda^a)`
  is `a|_(R_C)` on every such class, because `a|_(R_C)` unfolds to `a|_(L_C)`
  at a clean member (item 5 of the membership node) and unfolding is a
  bijection. By the same fact every copy whose `U` is clean is then clean.
  Copies whose `U` is dirty have mass `eps_out(a)`, since the law of `U` is
  uniform. So `d_kappa(lambda^a) <= eps_out(a)`.
* **Patchworks.** A copy is clean exactly when the class label, which is read
  at its representative, also unfolds correctly at the copy's own member. That
  is a restatement of the definition.

**Conclusion of Corollary A.** Suppose `o` has the property with confidence
`theta`. Take a YES instance and the witness `W`, `lambda`, `b` of the
hypothesis. The constraints of one folded aggregate are copies with the same
endpoints, so the disagreement mass of `W` against `hon_kappa(lambda, b)` is the
same, `<= zeta`, when it is measured on copies under `mu`. By (3),
`val_(U_(o')(G_multi))(W) >= 1 - xi`. By **(B_d) for patchworks**,
`H = hon_kappa(lambda, b)` is honest for `lambda` with dirt `d <= 1/64`. So
Theorem 3 applies to `(Phi_k, U_(o')(G_multi))` with `eps = 1/16`, `K' = 1`,
`xi + zeta <= 1/64` and `d <= 1/64`:

```text
c1 = 1 - 2 eps - 8 (xi + zeta + d) >= 1 - 1/8 - 1/4 = 5/8,
p0^2 c1 / 2 >= 5 p0^2 / 16 > p0^2 / 4 >= eps_k >= val on NO instances.
```

So `s := eps_k < p0^2 c1 / 2`. Theorem 3 puts the promise problem "YES instance
of `Gap3Lin(1 - eps_3, s*)` versus NO instance" in RP. It is NP-hard by (Q1),
so `NP in RP`. `square`

## Corollary B

Let `o` be as stated and `W = (A-labels, (sigma', b))` a YES labelling of
`U_o(G_folded)` of value `>= 1 - eta'`.

1. **Forget the bits.** Every `U_o` edge satisfied by `W` has a folded-accepted
   underlying pair. So `(A, sigma')` has `G_folded` value `>= 1 - eta'`.
2. **Pass to copies.** A folded constraint accepts only when every member
   multi-edge accepts, and weights are summed over members. So `(A, sigma')` has
   `G_multi` value `>= 1 - eta' >= 1 - eta_1`.
3. **Local rigidity.** `dkkms-grassmann-2to1-test-is-locally-99-percent-rigid`
   gives an outer labelling `lambda` with `val_(Phi_k)(lambda) >= 15/16` and
   `d_kappa(lambda) <= 1/64`, such that `(A, sigma')` agrees with
   `hon_kappa(lambda)` outside constraint mass `zeta_1`.
4. **Put the bits back.** Take `b` to be the bits of `W`. Then `W` agrees with
   `hon_kappa(lambda, b)` outside the same mass `zeta_1`.

So the hypothesis of Corollary A holds with `xi = eta'` and `zeta = zeta_1`.
Then `xi + zeta <= 1/128 + 1/128 = 1/64`, and Corollary A gives `NP in RP`.
The confidence `theta` is the selector's success probability. `square`

Corollary B is conditional. Its only unestablished input is the local rigidity
node, which is OPEN.

## Artifact

`experiments/ugc-selector-rigidity-2026-09-17/check_high_advantage_decoder.py`
checks Theorem 3 exactly on 60 random toy instances, with no sampling of the
decoder's coins. The run prints `ALL CHECKS PASSED`, with 59 trials having a
positive bound. In 30 of those, Theorem 1's bound `p^2 - 2 eps` is negative.
It does not check the DKKMS corollaries, which are pure bookkeeping on imported
facts.
