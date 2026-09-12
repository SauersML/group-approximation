---
rg: 2
id: homogeneous-full-square-zero-section-proof
kind: route
title: Primitive ideals of a matrix bundle algebra are point evaluations
target: homogeneous-full-square-zero-is-nilpotent-section
requires: []
---

`A=Gamma(X, End E)` is a unital locally trivial `M_n`-bundle algebra.  For
each `t`, evaluation `ev_t:A->End(E_t)` is surjective: on a trivializing
neighbourhood any matrix extends to a local constant section, and a cutoff
function extends it by zero.  Every irreducible representation of `A` is
equivalent to some `ev_t`, because `A` is an `M_n`-bundle over `X` with centre
`C(X)`: an irreducible representation restricts to a character of the centre,
i.e. a point `t`, and then factors through the fibre `M_n`.  So the primitive
ideals are `ker ev_t`, `t in X`.

A closed two-sided ideal is the intersection of the primitive ideals containing
it.  Hence `Ideal(x)=A` exactly when no `ker ev_t` contains `x`, i.e. when
`x_t != 0` for every `t`.

A square-zero element is the same thing as a section of the bundle of
square-zero endomorphisms, and it is full exactly when that section avoids zero
in every fibre, i.e. when it is a section of `N_0(E)`.
