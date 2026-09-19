---
rg: 2
id: fournier-facio-generator-support-component-proof
kind: route
title: Close generator supports under words and restrict a positive bounded-component stratum
target: fournier-facio-generator-support-components-escape-cutoffs
requires:
  - fournier-facio-bounded-block-near-witness-impossible
  - fournier-facio-charge-null-monomial-perturbations-impossible
---

Let `N_mu` be the left null ideal of the charged diagonal state.  From
`(FSC1)` and the null-ideal invariance calculation, `phi_mu` is invariant
under every `Ad(B_s)`.  Therefore `N_mu` is also stable under right
multiplication by every `B_s`.

Choose a word

```text
g=s_1...s_l,                 s_j in S,
B_g=B_(s_1)...B_(s_l).                              (FSCP1)
```

Iterating the near-multiplication rows gives

```text
pi(g)-pi(s_1)...pi(s_l) in N_mu.                    (FSCP2)
```

The exact telescoping identity

```text
pi(s_1)...pi(s_l)-B_(s_1)...B_(s_l)
 =sum_(j=1)^l pi(s_1)...pi(s_(j-1))
                  (pi(s_j)-B_(s_j))B_(s_(j+1))...B_(s_l)               (FSCP3)
```

puts every summand in `N_mu`: the prefix is handled by the left-ideal
property and the suffix by right stability under the comparison unitaries.
Consequently

```text
pi(g)-B_g in N_mu.                                  (FSCP4)
```

Different words for `g` give comparison products equal modulo `N_mu`, which
is all the charged near model uses.

By construction every `B_s` and `B_s^*` preserves each connected component
of the support graph.  Hence every product `(FSCP1)` preserves it too.  Put

```text
X_(<=m)={x in X:|C(x)|<=m}.                          (FSCP5)
```

This set is invariant under every comparison product.  If
`c=mu(X_(<=m))>0`, restrict the charged state to `X_(<=m)` and divide by
`c`.  Equations `(FSCP2)--(FSCP4)` show that all multiplication and
essential-freeness exceptional sets remain null after restriction.  The
result is a Fournier--Facio charged near witness, modulo null errors, on a
common block system whose blocks have dimension at most `m`.  This is
excluded by `fournier-facio-bounded-block-near-witness-impossible`.
Therefore `c=0`, proving `(FSC2)`.
