---
rg: 2
id: sofic-nielsen-chart-model-proof
kind: route
title: Put independent sign coordinates over each good local orbit chart
target: sofic-nielsen-charts-defeat-uniform-compact-collapse
requires:
  - monomial-ascending-hnn-coset-action-sofic
---

The properness assertion in `(SNC2)` is the usual ascending-HNN coset test:
`t^(-1) gamma t Gamma=Gamma` would imply `gamma in alpha(Gamma)`.  The
elementary matrix `e_12(x)` is outside the image because every polynomial
entry in that image belongs to `F_2[x^2]`.

Fix finite sets `F in V`, `E in X` containing `o,x_*` and all translates
needed by the desired covariance tests, and let `epsilon>0`.
`monomial-ascending-hnn-coset-action-sofic` supplies a finite set `A`, a map
`phi:V->Sym(A)`, a finite label set `C`, a good set
`S subset A` with `|S|>(1-epsilon)|A|`, and injective charts

```text
pi_s:E -> C,        s in S,                               (SNP1)
```

such that `phi` is `(F,epsilon)`-multiplicative and

```text
pi_(phi(g)s)(g x)=pi_s(x)                                 (SNP2)
```

whenever all displayed data lie in the prescribed windows and both chart
indices are good.  This is the orbit-approximation identity with `g x`
substituted for its site variable.

Let `D_C=directSum_C C_2`, write `r_c` for its canonical sign unitaries, and
put

```text
B=directSum_(s in A) L(D_C),
tau_B=|A|^(-1) sum_s tau_(D_C).                           (SNP3)
```

This is a finite-dimensional commutative tracial C-star algebra.  Define
`beta_g` by permuting its direct summands through `phi(g)` and acting
identically inside each copy of `L(D_C)`.

For `x in E-{o}`, define the `s` block of `theta(b_x)` on a good chart by

```text
theta(b_x)_s=r_(pi_s(x)) r_(pi_s(o));                     (SNP4)
```

on bad blocks set it equal to one, and assign arbitrary involutions to the
remaining free generators.  Since `N` is free on the displayed `b_x`, these
assignments extend uniquely to an exact homomorphism `theta:N->U(B)`.

On a block `phi(g)s` for which `(SNP2)` applies, cancellation of the two
basepoint labels gives

```text
theta(alpha_g(b_x))_(phi(g)s)
 =r_(pi_(phi(g)s)(g x)) r_(pi_(phi(g)s)(g o))
 =r_(pi_s(x)) r_(pi_s(o))
 =beta_g(theta(b_x))_(phi(g)s).                          (SNP5)
```

At most `2 epsilon |A|` blocks fail because one endpoint is outside `S`;
each difference of unitaries has norm at most two.  Therefore every generator
covariance defect is at most

```text
2 sqrt(2 epsilon).                                       (SNP6)
```

Fixed products cost only their fixed word length by telescoping.  Likewise,
the `(F,epsilon)`-multiplicativity of `phi` implies

```text
||beta_g beta_k(theta(u))-beta_(gk)(theta(u))||_2
 <=2 sqrt(epsilon)                                       (SNP7)
```

for each tested unitary block word `theta(u)`, again followed by a fixed
word-length factor when needed.  Choosing exhausting windows and
`epsilon->0` proves `(SNC5)`.

Finally, injectivity of every good chart gives
`pi_s(x_*)!=pi_s(o)`.  Hence the good block of `theta(b_(x_*))` is a
nonidentity group unitary in `L(D_C)`, has trace zero, and has squared distance
two from one.  Since bad blocks were assigned the identity, consequently

```text
||theta(b_(x_*))-1||_2^2 = 2 |S|/|A|
                         > 2(1-epsilon),                 (SNP8)
```

which proves `(SNC6)`.  Setting the bad blocks to independent unequal labels
instead of one makes equality `2` hold, but the lower bound is all the
no-modulus statement needs.
