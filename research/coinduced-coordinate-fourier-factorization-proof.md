---
rg: 2
id: coinduced-coordinate-fourier-factorization-proof
kind: route
title: Group the coinduced Fourier character by independent coset coordinates
target: coinduced-coordinate-fourier-test-factorizes
requires:
  - infinite-label-process-is-haar-linear-iff-fourier-binary
---

Choose a section `s:Lambda/H->Lambda` with `s(H)=e`, and write

```text
c(g,z)=s(gz)^(-1) g s(z) in H,
(g.y)_(gz)=c(g,z).y_z.                                  (CFF1)
```

For the label in `(CFT1)` and `g in Lambda`, direct substitution gives

```text
F_i(g^(-1).y)=f_i(c(g^(-1),gH).y_(gH)).                 (CFF2)
```

Take a finitely supported coefficient array `a_(g,i)`.  Group its exponent
using the coset `z=gH`.  Formula `(CFF2)` writes the corresponding random
character as a product

```text
product_(z in Lambda/H) chi_p(Psi_z(y_z)),              (CFF3)
```

where only finitely many factors are nontrivial and every `Psi_z` is a finite
`F_p`-linear combination of `H`-translates of the source labels.  Product
measure makes the coordinates `y_z` independent, so

```text
M_Y(a)=product_z M_X(a_z).                              (CFF4)
```

If all source moments lie in `{0,1}`, `(CFF4)` puts every coinduced moment in
`{0,1}`.  Conversely, restrict `a` to group elements `g in H`.  Then `gH=H`
and, because `s(H)=e`, `(CFF2)` is exactly the original `H`-translate name at
the base coordinate.  Every source moment therefore occurs verbatim as an
upstairs moment.  The two zero-or-one tests are equivalent, and
`infinite-label-process-is-haar-linear-iff-fourier-binary` converts this to
the asserted equivalence of Haar linearity.

Finally, the translates of `(CFT1)` recover at coordinate `z=gH` all
`H`-translated source labels (the cocycle merely reindexes them).  If those
labels generate `X`, the recovered families generate each coordinate
probability algebra, hence their countable union generates the product
probability algebra of `Y`.
