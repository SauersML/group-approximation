---
rg: 2
id: dyadic-perturbation-soficity-proof
kind: route
title: Finite dyadic orbits give local residual finiteness, and a cyclic interval models the dilation
target: dyadic-perturbation-group-is-sofic
requires:
  - dyadic-finite-perturbation-group-elementary-structure
artifacts:
  - research/artifacts/dyadic-finite-perturbation-sofic-non-mf-2026-09-08.md
---

## Step 1: `R` is locally residually finite

**Finite orbits.**  Fix `x = v + 2^k Z^3` and `j >= 0`.  Choose an
integer `s` with `s >= j`, `s >= -k`, `s >= 0` and `v in 2^-s Z^3`.
Integral matrices and translations in `2^-j Z^3 <= 2^-s Z^3` preserve
`2^-s Z^3`, and they do not change the scale `k`.  So the `N_j`-orbit of
`x` is contained in the finite set of cosets `2^-s Z^3 / 2^k Z^3`.

**Each `N_j` is residually finite.**  Scaling the translation coordinate
by `2^j` identifies `N_j` with `Z^3 x| SL_3(Z)`, which embeds in
`GL_4(Z)` as integral affine matrices; reduction modulo an integer not
dividing a nonzero entry of `M - I` separates a chosen nonidentity `M`.

**Local residual finiteness.**  Given finitely many elements of `R`,
their `N`-coordinates lie in a single `N_j`, and the supports of their
finitary coordinates lie in a finite set.  Let `O` be the union of the
`N_j`-orbits of that finite set: it is finite by the first paragraph and
`N_j`-invariant.  The subgroup generated lies in `Sym(O) x| N_j`, which
is residually finite: a nonidentity `N_j`-coordinate is detected by a
finite quotient of `N_j`, and an element with trivial `N_j`-coordinate
and nontrivial permutation coordinate is detected by the finite quotient
`Sym(O) x| image(N_j -> Sym(O))`.

## Step 2: explicit models for the dilation extension

Let `R` be locally residually finite and `alpha` an automorphism.  Fix a
finite test set `E` of `R x|_alpha Z`, closed under the products and
inverses to be tested, with elements written `(r,m)`.  Take `M` larger
than every `|m|` involved and `I = Z/MZ`.  Collect the finitely many
`alpha^-t(r)` for `t in I` and `(r,m) in E` into a finitely generated,
hence residually finite, subgroup `R_0`, and choose a finite quotient
`theta : R_0 -> Q` separating every nonidentity element of that
collection.  Define permutations of `I x Q` by

```text
sigma_((r,m))(j,q) = (t, theta(alpha^-t(r)) q),
t = j + m mod M, taken in I.                                      (1)
```

Each is a bijection: the shift is one and each fibre map is left
multiplication in `Q`.  Whenever `j`, `j+n` and `j+n+m` are all in `I` as
integers,

```text
sigma_((r,m)) sigma_((s,n)) (j,q) = sigma_((r alpha^m(s), m+n))(j,q),
```
because the two fibre multipliers compose to
`theta(alpha^-(j+n+m)(r)) theta(alpha^-(j+n)(s))
 = theta(alpha^-(j+n+m)(r alpha^m(s)))`.  The excluded set is where a
tested shift crosses an endpoint, of proportion at most `(|n|+|m|)/M`.

Separation: if `m != 0` the first coordinate moves once `M > |m|`, so
there are no fixed points; if `m = 0` and `r != 1` then `theta` was
chosen to separate every `alpha^-j(r)`, and nonidentity left
multiplication on `Q` is fixed-point free.  `(1,0)` gives the identity.
For distinct `g,h` test `h^-1 g`.  Letting `M` grow and exhausting the
countable group by finite test sets gives sofic approximations.

## Conclusion

Apply Step 2 to `R` from `(SF1)` with `alpha` conjugation by the dilation
`a`.  Then `G = R x| <a>` is sofic.  Hyperlinearity follows from
`||P_sigma - P_tau||_2^2 = 2 d_Ham(sigma,tau)`, which turns the sofic
models into normalized Hilbert--Schmidt models separating nonidentity
elements.
