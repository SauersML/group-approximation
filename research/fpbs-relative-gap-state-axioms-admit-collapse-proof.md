---
rg: 2
id: fpbs-relative-gap-state-axioms-admit-collapse-proof
kind: route
title: The theta-squared floor of the collapse state sums to infinity over every infinite coset, while everything at or below p_c is Bernoulli
target: fpbs-relative-gap-state-axioms-admit-collapse
requires:
  - fpbs-two-point-state-axioms-admit-collapse
  - fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2
  - fpbs-fibre-summed-connectivity-operator
---

Notation as in the target.

## Step 1 (import)

`fpbs-two-point-state-axioms-admit-collapse` (ESTABLISHED), Theorem item 2,
verbatim: "Define `f_p = tau_p` for `p <= p_c`, and
`f_p = theta(p)^2 + (1 - theta(p)^2) tau_(p_c)` for `p > p_c`, with
`u = 1{p > p_c}`. Then `f` satisfies (T1)–(T8)." This is item 1 of the
target. The equality `f_p = tau_p` for `p <= p_c` is the definition.

## Step 2 (the floor)

Let `p > p_c`. By definition of `p_c(G) = sup{p : theta(p) = 0}` and
monotonicity of `theta`, `theta(p) > 0`. Since `0 <= tau_(p_c) <= 1` and
`1 - theta(p)^2 >= 0`, for every `y` in `Gamma`

```text
f_p(y) >= theta(p)^2 > 0.
```

Let `I` be an infinite subgroup and `xI` a coset. Then `xI` is infinite and
`sigma^I_(f_p)(xI) >= theta(p)^2 |xI| = infinity`. Taking `x = e` gives
`chi^I(f_p) = infinity` for every `p > p_c`. For `p < p_c`,
`chi^I(f_p) = chi^I_p <= chi_p < infinity`, the susceptibility being finite
below `p_c` on every transitive graph (Aizenman--Barsky, Menshikov). Hence
`p_c(I; f) = p_c(G)`. For normal `I = N` and nonnegative `v != 0` on
`Q = Gamma/N`, pick `q'` with `v(q') > 0`; then
`(S^f_p v)(q) >= sigma^N_(f_p)(q'^(-1) q) v(q') = infinity` for every `q`.
This is item 2.

## Step 3 (critical data)

For `p <= p_c` every value `f_p(y)` equals `tau_p(y)`. Every datum listed in
item 3 (`chi^N_(p_c)`, `sigma_(p_c)`, `||S_(p_c)||`, the type of the pair) is
a function of `(tau_p)_(p <= p_c)` and the group, so it is the same for `f`
and for Bernoulli. `rho_Q`, `rho_Gamma` and cogrowth do not involve `g`.

## Step 4 (the kill)

Suppose a state-level relative argument, as defined in item 4, proved
`p_c(G) < p_c(N;G)` on some pair. Its hypotheses hold for `f` (Steps 1 and 3),
so it would give some `p > p_c` with `chi^N(f_p) < infinity`, contradicting
Step 2.

## Step 5 (type-(i) pairs)

`fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2` (ESTABLISHED), item 3,
verbatim: "If `||S_(p_c)||=M_Q<infinity`, then for `0<delta<1/(d M_Q)` with
`p_c+delta<=1`, `chi^N_(p_c+delta) <= M^N(delta) <= M_Q/(1-d delta M_Q)`, so
`p_c(G)<p_c(N;G)`." So Bernoulli has the gap on type-(i) pairs. By Step 3,
`||S^f_(p_c)|| = ||S_(p_c)|| < infinity`, and `f` satisfies (T8) by Step 1,
while Step 2 gives `chi^N(f_(p_c+delta)) = infinity` for every `delta > 0`.
So the conclusion of that item does not follow from (T1)--(T8) plus
critical data. Its proof therefore uses an input outside the axioms; the one
it uses is the truncated majorant of
`fpbs-bk-majorant-integrated-sensitivity-is-critical-l2-proof` Step 4e,
cited in the setting of the imported node.

For the last sentence of item 5: `fpbs-fibre-summed-connectivity-operator`
(ESTABLISHED), verbatim: "Then for every `p`,
`||T_p||_{l2(Gamma) -> l2(Gamma)}  <=  ||S_p||_{l2(Q) -> l2(Q)}`". So
`||T_(p_c)|| < infinity`, and `fpbs-two-point-state-axioms-admit-collapse`
item 3, verbatim: "Suppose `||T_(p_c)||_(2->2) < infinity`. ... Then `f`
admits no *truncation system*." QED.
