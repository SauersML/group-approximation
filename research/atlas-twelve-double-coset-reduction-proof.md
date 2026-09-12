---
rg: 2
id: atlas-twelve-double-coset-reduction-proof
kind: route
title: Decompose cyclic commutants and eliminate the common relative unitary
target: atlas-common-u-is-twelve-double-coset-system
requires:
  - atlas-a4-packet-biclique-decomposition
  - atlas-a4-packet-centralizer-product-compiler
  - atlas-shifted-factorizations-have-independent-right-gauge
---

The biclique theorem identifies twelve distinct order-two/order-three pair
constraints.  In defect zero, the shifted-centralizer compiler says exactly
that their common frame belongs to the corresponding twelve products

```text
U in U(rho(C_3)') R U(rho(C_2)'),
```

with the stated reversal convention.  Choose witnesses `X_e,Y_e`.  Eliminating
`U` by comparison with one reference edge gives the eleven product equations
in `(CUL3)`; substituting the same reference product into the collision word
gives the last equation.  Conversely a solution of `(CUL3)` defines one `U`
in every required shifted product and makes collision exact, proving the
equivalence.

Since `rho|_(C_m)` is `(D/m)` copies of `Reg(C_m)` and all irreducibles of a
cyclic group are one-dimensional, its commutant algebra is

```text
directSum_(chi in dual(C_m)) M_(D/m)(C),
```

which proves `(CUL1)`.  The regular A8 decomposition

```text
rho=directSum_pi pi tensor C^(k dim(pi))
```

gives `Q(k)` in `(CUL4)`.  Every member of `Q(k)` commutes with `R`, so the
displayed gauge leaves `X_eRY_e` fixed.  Independence over the twelve edges is
the established right-gauge theorem, proving `(CUL5)` and the rectangle
noncanonicity statement.

Unitary conditions and `(CUL3)` are polynomial equations in real and
imaginary matrix entries with algebraic coefficients.  Compactness is
automatic.  Standard real closed-field transfer gives an algebraic point
whenever the fixed-`k` semialgebraic set is nonempty.  Finally tensoring every
unknown and coefficient with `I_l` embeds a solution at `k` into the system at
`lk`; it does not compress a general large-`k` solution.  The established
finite-tracial escape recorded in the four-cycle Dirichlet compiler proves
the final semantic boundary.
