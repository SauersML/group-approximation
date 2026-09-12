---
rg: 2
id: localized-tail-qutrit-wrapper-reflection-proof
kind: route
title: Split localized tail copies over the finite leaf permutation action
target: localized-tail-qutrit-wrappers-reflect-hyperlinearity
requires:
  - single-leaf-off-code-qutrit-bridges-are-virtually-abelian
  - amenable-quotient-preserves-metric-approximability
  - finite-support-corner-localizes-obstruction
  - leavitt-cylinder-swaps-generate-thompson-in-el
  - leavitt-gl-equals-el-and-perfect-unit-group
  - thompson-v-lifts-through-binary-leavitt-steinberg-cover
---

Use the standard prefix-permutation action

```text
f(d xi)=f(d) xi,                       d in D,           (LTW4)
```

so the stabilizer in `F` of a leaf fixes its whole cylinder pointwise.
For each `d in D`, choose `f_d in F` with `f_d(d_0)=d` and define

```text
A_d=f_d A f_d^(-1).                                     (LTW5)
```

The subgroup `A_d` is independent of the choice of `f_d`, because two
choices differ by the pointwise cylinder stabilizer.  It is supported inside
`[d]`.

Consequently `A_d` and `A_e` commute for `d!=e`.  Their product is
an internal direct product: if

```text
product_(d in D) a_d=1,                    a_d in A_d,
```

then restriction to `[d]` gives `a_d=1`.  Put

```text
N=product_(d in D) A_d isomorphic to A^D.               (LTW6)
```

Conjugation by `f in F` sends `A_d` to `A_(fd)`, so `N` is
normal in `Gamma=<F,A>`.  Every word in `F union A` rewrites into
`NF`.  Also `N intersect F={1}`: an element of `N` preserves every
leaf cylinder, while an element of the faithful standard `Sym(D)` copy
with trivial leaf permutation is the identity on every cylinder.  Therefore

```text
Gamma=N semidirect F isomorphic to A^D semidirect F,
```

which proves `(LTW1)`.

Hyperlinearity passes to subgroups, so hyperlinearity of `Gamma` implies
that of its base coordinate `A_(d_0)=A`.  Conversely, if `A` is
hyperlinear, then its finite direct power `A^D` is hyperlinear: take
finite Cartesian products of unitary microstates, or equivalently tensor the
corresponding Connes-embeddable group factors.  The exact sequence

```text
1 -> A^D -> Gamma -> F -> 1                             (LTW7)
```

has finite, hence amenable, quotient.  Amenable-quotient permanence for
hyperlinearity makes `Gamma` hyperlinear.  This proves `(LTW2)`.

Now allow any finite collection of qutrit cells conjugated by elements of
`Gamma` and any algebraic projection or overlap coefficient supported in
`C[Gamma]`.  If these data completed a no-CE algebraic atlas, finite-support
localization would produce a finitely generated nonhyperlinear subgroup
`Lambda<=Gamma`.  If `A` were hyperlinear, then `Gamma`, and hence
all its subgroups, would be hyperlinear, a contradiction.  Therefore the
one-leaf source `A` must already be nonhyperlinear.

Nothing in this implication assumes that an overlap is a group conjugate, a
partial-isometry arrow, or a fixed-code permutation.  Arbitrary additive
multi-path coefficients remain inside `C[Gamma]` and are covered by the
same support argument.

Finally, both the binary-Leavitt cylinder-swap map and the established
Steinberg lift are injective on `V`.  They therefore carry `(LTW1)` to
an isomorphic subgroup rather than changing its extension class.  This proves
the host variants and the stated boundary.
