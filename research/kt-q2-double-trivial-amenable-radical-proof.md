---
rg: 2
id: kt-q2-double-trivial-amenable-radical-proof
kind: route
title: Kill the polynomial core and use the faithful Bass--Serre action
target: kt-q2-double-has-trivial-amenable-radical
requires: []
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
---

Write `R_+=F_2[x_1,...,x_d]` and
`R=F_2[x_1^(+-1),...,x_d^(+-1)]`.  First let `K normal G` with
`K<=Gamma`, and take `z=(z_kl) in K`.  For `i!=j`, `a in R`, and
`E=E_ij`, normality gives

```text
(1+aE)z(1-aE)=z+a(Ez-zE)-a^2 EzE in K<=EL_r(R_+).       (QAR1)
```

Put `a=x_1^(-m)` with `m` arbitrarily large.  For `k!=j`, the `(i,k)` entry
of `(QAR1)` is `z_ik+x_1^(-m)z_jk`.  It lies in `R_+` for every `m`, so
`z_jk=0`.  Varying `j` makes `z` diagonal.  The `(i,j)` entry is then
`x_1^(-m)(z_jj-z_ii)`, so all diagonal entries agree.  Thus `z=c1`; because
`z` is invertible over `R_+`, `c` is a unit, and the only unit of this
polynomial ring is `1`.  Therefore `core_G(Gamma)={1}`.

Let `T` be the Bass--Serre tree of `D=G *_Gamma G`.  An element in the kernel
of `D` acting on `T` belongs to a vertex stabilizer and to every incident edge
stabilizer, hence to `core_G(Gamma)`.  Thus the action is faithful.  The
standard action of this reduced amalgam is minimal; it is non-elementary
because both edge inclusions are proper and `[G:Gamma]=infinity` (the
projection to `SL_d(Z)` is trivial on `Gamma`).

Now let `A normal D` be amenable.  An amenable tree action is elementary.  If
`A` contains a hyperbolic element, the canonical limit set of `A` in
`partial T` has at most two points.  Normality makes that canonical set
`D`-invariant, contrary to non-elementarity of the `D`-action.  If every
element of `A` is elliptic but `A` has no global fixed vertex, the standard
elliptic-action lemma gives a unique fixed end.  Normality makes that unique
end `D`-invariant, again a contradiction.  Therefore `A` has a nonempty
fixed subtree.  Normality makes this subtree `D`-invariant; minimality makes
it all of `T`; faithfulness then gives `A={1}`.
