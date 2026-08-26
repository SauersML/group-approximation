---
rg: 2
id: asymmetric-prefix-signed-hecke-return-proof
kind: route
title: Expose each external coefficient with one constant Hecke root
target: one-asymmetric-prefix-cannot-be-signed-hecke-return
requires:
  - signed-hecke-normalizer-has-eight-external-root-returns
---

For roots `x_ab(c)` and `x_bj(1)` with `a!=j`, the characteristic-two
Steinberg formula gives

```text
x_ab(c)x_bj(1)x_ab(c)^(-1)=x_bj(1)x_aj(c).            (APRP1)
```

For `x_ia(1)` it analogously exposes `x_ib(c)`.  Substitution in the eight
rows of `(APR1)` gives the displayed output positions.  Both the witness
and output positions occur among the ten constant roots generating `L_0`.

Every product of those generators is an elementary matrix all of whose
entries are in the embedded copy of `F_2`; this follows directly by matrix
multiplication and needs no classification of `L_0`.  Therefore membership
of `x_exposed(c)` in `L_0` forces its unique off-diagonal entry `c` to lie in
`F_2`, proving `(APR2)`.

Finally, the Steinberg commutator formula and the binary Leavitt relation
`t_i s_j=delta_(i,j)` give

```text
[x_(a,k)(s_mu t_i),x_(k,b)(s_j t_nu)]
 =x_(a,b)(s_mu(t_i s_j)t_nu)
 =x_(a,b)(delta_(i,j)s_mu t_nu),                      (APRP2)
```

which is `(APR3)`.  The standard reduced Leavitt matrix units
`s_mu t_nu` with a nonempty displayed prefix are neither zero nor one; in
the diagonal case their complement is the other nonzero binary branch.
This completes the single-insertion and normalizer-sandwich arguments.
