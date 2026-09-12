---
rg: 2
id: hs-dehn-modulus-bounded-by-dehn-function
kind: claim
title: The HS-Dehn modulus of a finite presentation is dominated by its Dehn function
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  quantitative-higman-embedding-with-dehn-control: that bounds the relative Dehn function of a subgroup inside a Higman host; this defines a new invariant measuring HS defect of trivial words against length and proves only the trivial area comparison.
  conjugacy-compressed-dimension-trigger: that is the exact zero-loss identity for one conjugated relator; this is the general area-weighted bound for every trivial word, of which the conjugate case is the area-one instance.
---

Fix a finite presentation `G=<S|R>`, `S={s_1,...,s_m}`, and for a tuple `U`
of `d x d` unitaries write `Def_R(U)=max_(r in R)||r(U)-I||_2` in the
normalized Hilbert--Schmidt norm.  Define the **HS-Dehn modulus**

```text
F_G(l) = sup { ||w(U)-I||_2 / Def_R(U) :
               |w|<=l, w=_G 1, d>=1, U in U(d)^m, Def_R(U)>0 }.
```

Then for every `l`,

```text
F_G(l) <= Dehn_G(l).                                         (HSD1)
```

*Proof.*  For unitaries `||AB-I||_2<=||A-I||_2+||B-I||_2` and
`||grg^(-1)-I||_2=||r-I||_2`, and free reduction does not change `w(U)`.
A trivial word of area `N` is freely a product of `N` conjugates of
relators, so `||w(U)-I||_2<=N Def_R(U)`.

Consequently `F_G` is finite, and it is bounded by a computable function
whenever the word problem of `G` is solvable.  Say that `G` has
**computable HS length control** if there is a computable
`Phi:N x Q_(>0)->Q_(>=0)` with `Phi(l,t)->0` as `t->0^+` for each `l` such
that `w=_G 1` and `Def_R(U)<=t` imply `||w(U)-I||_2<=Phi(|w|,t)`.  The area
modulus `Phi(l,t)=Dehn_G(l) t` is computable exactly when the word problem
is solvable; an HS-stability modulus gives `Phi(l,t)=l eps(t)`.  The
property does not depend on the finite presentation.

The invariant isolates what every HS-PCP compiler must achieve: a defect
bound for trivial words that beats area.  See
`hyperlinear-computable-hs-dehn-modulus-solvable-word-problem`.
