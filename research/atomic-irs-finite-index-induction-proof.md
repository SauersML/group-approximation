---
rg: 2
id: atomic-irs-finite-index-induction-proof
kind: route
title: Identify a finite-orbit IRS character with a finite-index induced regular character
target: atomic-noncohyperlinear-irs-forces-nonhyperlinear
requires: []
---

Let `H` be an atom.  Invariance makes every conjugate of `H` an atom of the
same mass.  There can therefore be only finitely many conjugates.  Ergodicity
says their orbit has total mass one, so the law is uniform on that orbit.
Its stabilizer is `Delta=N_Gamma(H)`, whence
`[Gamma:Delta]<infinity` and `H normal Delta`.

Let `q:Delta->K=Delta/H`, let `lambda_K` be the regular representation, and
choose left-coset representatives `r_1,...,r_m` for `Gamma/Delta`.  The
finite-index induced representation is the cocycle matrix

```text
rho(g)_(j,i)=
  lambda_K(q(r_j^(-1) g r_i))
       if r_j^(-1) g r_i is in Delta,
  0    otherwise.                                      (AIP1)
```

For every `g`, each column and row has exactly one nonzero unitary entry, so
`rho` is a unitary representation in `M_m(L(K))`.  Its normalized trace is

```text
(tr_m tensor tau_K)(rho(g))
 =m^(-1) sum_(i:r_i^(-1)gr_i in Delta)
       delta_e(q(r_i^(-1)gr_i))
 =m^(-1) sum_i 1_(r_i^(-1)gr_i in H)
 =chi_mu(g).                                           (AIP2)
```

The trace-preserving GNS uniqueness theorem therefore identifies the GNS
algebra of `chi_mu` with `W*(rho(Gamma))`, a tracial von Neumann subalgebra
of `M_m(L(K))`.  Connes embeddability passes to matrix amplifications and
von Neumann subalgebras.  Hence Connes embeddability of `L(K)` would imply
Connes embeddability of the IRS GNS algebra.  Taking the contrapositive proves
`(ANI3)`.

For the converse scope statement, take a finite-rank free group surjecting
onto a finitely generated non-hyperlinear group (finite generation is
available by `hyperlinear-quotient-permanence-equivalence`).  The kernel is
normal, so its Dirac mass is an IRS, and its membership character is exactly
the pulled-back regular character of the quotient.
