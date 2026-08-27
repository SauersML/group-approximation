---
rg: 2
id: hnn-profinite-edge-screening-proof
kind: route
title: Map to a finite-base HNN extension and separate once more
target: hnn-mark-collapse-requires-profinite-edge-incompatibility
requires: []
---

The kernel equality in `(PIC2)` makes

```text
theta_bar(q(a))=q(theta(a))                              (PIC4)
```

well-defined and bijective from `q(A)` to `q(B)`.  Hence the quotient map on
the base and the stable letter define a homomorphism

```text
H -> H_Q=<Q,s | s x s^(-1)=theta_bar(x), x in q(A)>.     (PIC5)
```

The image of `w` is `q(w)!=1`; Britton's lemma embeds the finite base `Q` in
`H_Q`.  The group `H_Q` is the fundamental group of a finite graph of finite
groups, so it is virtually free and residually finite.  Some finite quotient
of `H_Q` therefore keeps `q(w)` nontrivial.  Composing with `(PIC5)` gives the
required finite quotient of `H`.

A finite quotient yields a finite permutation representation by its regular
action.  Thus the contrapositive applies to the assertion that all exact
finite-dimensional unitary representations kill `w`.
