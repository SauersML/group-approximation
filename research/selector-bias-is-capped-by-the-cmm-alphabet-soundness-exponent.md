---
rg: 2
id: selector-bias-is-capped-by-the-cmm-alphabet-soundness-exponent
kind: claim
title: A polynomial-time branch selector with YES orientation-lift value c on 2-to-1 reductions of soundness delta and left alphabet K puts the source in RP once delta < K^(-(1-c)/(1+c)-o(1)), so bias c needs alphabet K >= delta^(-(1+c)/(1-c)+o(1)), and at the CMM-optimal 2-to-1 exponent 1/3 no bias above one half survives
distinct_from:
  orientation-lift-selectors-need-vanishing-host-gap: that prices selectors in the host spectral gap (lambda_2 < X(delta) eta') by AKKSTV rounding, and is vacuous on every host with small gap and at every constant bias; this prices them in the alphabet by CMM low-value rounding, is independent of the host, and bites at constant bias.
  near-perfect-selectors-die-on-every-rigid-doubled-lec: that kills near-1 selectors (lift value 1 - 10^(-5)) on reductions with a linear read-out, comparable marginals, tight outer soundness and 99 percent rigidity; this assumes none of these, covers every bias c in (1/2, 1), and kills only when the alphabet is small against the soundness.
  constant-bias-selectors-need-seed-dishonest-witnesses: that reduces the constant-bias cell on doubled LECs to a statement on seed labels; this puts an instance-free, witness-free alphabet price on the whole cell.
  sqrt-scale-ug-hardness-costs-alphabet-exp-c-squared: that prices sqrt-scale unique-games hardness near completeness 1 via CMM Theorem 4.5; this prices orientation lifts of 2-to-1 games at every completeness via CMM Theorem 3.1, and identifies the trivial orientation with the CMM d-to-1 exponent.
artifacts:
  - experiments/ugc-cmm-selector-exponent-2026-09-17/check_cmm_selector_exponent.py
---

**ESTABLISHED.** Route: `selector-bias-cmm-exponent-proof`.

## Setting

`G(x)` is a weighted bipartite 2-to-1 game in the setting of
`orientation-lifts-sandwich-2to1-game-values`. Its left alphabet is `[K]`, with
`K = K(x) = 2k`, and its right alphabet is `[k]`. The weights are integer
multiplicities of total at most `poly(|x|)`. An orientation `o` and its lift
`U_o`, a unique game on `[K]`, are as in that node. Put

```text
e(eps)    :=  eps / (2 - eps)                  (the CMM exponent),
g(eps, K) :=  the bound of cmm-unique-games-low-value-rounding.
```

## Statement

**Theorem K.** Let `Lang = (Y, N)` be a promise problem. Let `x -> G(x)` be a
polynomial-time map as above. Let `delta(x)` be a polynomial-time computable
rational, and let `S` be a randomized polynomial-time algorithm that outputs an
orientation `S(x)` of `G(x)`. Suppose that:

* **(Y)** for `x in Y`: `Pr_S[val(U_(S(x))) >= 1 - eps(x)] >= theta(|x|)`,
  with `theta >= 1/poly`, and `g(eps(x), K(x)) >= delta(x) + 1/p(|x|)` for a
  polynomial `p`;
* **(N)** for `x in N`: `val(G(x)) <= delta(x)`.

Then `Lang in RP`. The error is one-sided, and each trial succeeds with
probability at least `theta/p`.

**Corollary K1 (exponent form).** Let `(G_j, S_j)_j` be a sequence of such
reductions and selectors for `Lang`. Let `G_j` have left alphabet `K_j -> infinity`
and NO soundness `delta_j`, and let `S_j` have YES lift value `c = 1 - eps` for a
constant `eps in [0, 1)`. Let

```text
s  :=  liminf_j  log(1/delta_j) / log K_j        (alphabet-soundness exponent).
```

If `s > e(1 - c) = (1 - c)/(1 + c)`, equivalently `c > (1 - s)/(1 + s)`, then
`Lang in RP` (via every `j` large enough). So, unless the source is in RP,
every selector route at bias `c` runs on reductions with

```text
K  >=  delta^( -(1 + c)/(1 - c) + o(1) ).
```

At `c -> 1/2` the price is `K >= delta^(-3+o(1))`. For `c = 1 - eps` near 1 it
is `K >= delta^(-2/eps + O(1))`, which is CMM's price on UGC itself.

**Corollary K2 (the trivial selector is the CMM 2-to-1 exponent).** Any fixed
rule, such as "the smaller label of each fibre gets bit 0", is a
polynomial-time orientation. By the sandwich, its lift has value at least
`val(G)/2`. So a 2-to-1 reduction with YES value `>= 1 - eta` feeds Theorem K
with `eps = (1 + eta)/2`, and

```text
e((1 + eta)/2)  =  (1 + eta)/(3 - eta).
```

Hence every 2-to-1 reduction from a source outside RP has
`s <= (1 + eta)/(3 - eta)`, which is `1/3` at perfect completeness. This is the
exponent of CMM Section 5 at `d = 2`, re-derived from Theorem 3.1 and the
sandwich alone.

**Corollary K3 (the one-half wall is where the two exponents meet).** Take a
2-to-1 family at the CMM limit of K2, with `s >= 1/3`. It admits no polynomial-time selector with YES lift value `c` for
any constant `c > 1/2`, unless the source is in RP. On such a family the
trivial orientation is optimal, up to `o(1)` in bias. The bias a selector may
reach grows only as the family gives up alphabet efficiency:
`c_max(s) = (1 - s)/(1 + s)`.

**Corollary K4 (near-1, from Theorem 4.5).** Let `A` be the constant of
`cmm-unique-games-sqrt-log-k-rounding`. A selector with YES lift value
`1 - eta'` also puts the source in RP when
`A sqrt(eta' ln K) <= (1 - delta)(1 - 1/p(|x|))`. So, unless the source is in
RP, near-1 selector routes need both of the following. The second is K1 at a
fixed `eta'`.

```text
eta'  >  (1 - delta)^2 (1 - o(1)) / (A^2 ln K)    and    eta'  >=  2 s / (1 + s).
```

## What it does, and what it does not do

* **Instance-free and witness-free.** No rigidity, read-out, marginal, seed or
  outer-game hypothesis is used. The only invariant is `s` against the bias.
  Every member dies at one step: CMM low-value rounding of the YES lift, pulled
  back through the sandwich to a `G`-labelling of value above `delta`, which no
  NO instance has.
* **It kills the constant-bias cell on alphabet-efficient reductions.** A future
  2-to-1 hardness theorem with polynomially small soundness
  `delta = K^(-s)` (`s > 0` fixed) is useless to the parity-leaking selector
  route above bias `(1 - s)/(1 + s)`. If `s -> 1/3`, it is useless at every
  bias above `1/2`.
* **It does not kill `parity-leaking-branch-selectors-reach-near-perfect-completeness`
  on DKKMS.** DKKMS soundness needs only `l >= l_0(delta)`, so `l`, and with it
  `K`, may grow freely at fixed `delta`. This sends `s -> 0` and makes the price
  vacuous at every bias. It is the same escape that defeats the spectral gate
  (`folded-dkkms-host-gap-vanishes-as-l-grows`). Only a selector whose bias
  degrades as `l` grows would be caught.
* It is an upper bound on what selectors can do. It says nothing about whether
  a selector exists at small `s`.

This neither proves nor refutes UGC.
