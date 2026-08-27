---
rg: 2
id: native-conjugate-heisenberg-overlap-proof
kind: route
title: Project the amalgamated free-product normal form onto reduced length three
target: native-conjugate-heisenberg-charts-share-only-edge-coefficients
requires:
  - selected-odd-heisenberg-corner-is-native-matrix-amalgam
---

Choose group-basis complements

```text
A=D direct-sum A_0,             C[H_p]=C[<w,c>] direct-sum H_0,   (NCP1)
```

spanned respectively by group elements outside the amalgamated subgroups.
After cutting by `e_chi`, this gives a vector-space complement

```text
M=D direct-sum M_0.                                  (NCP2)
```

The algebraic amalgamated-free-product normal form is a direct sum of `D`
and alternating relative tensor words in `A_0` and `M_0`.

Write `x=x_D+x_0` according to `(NCP2)`.  Since `a` is a group element of
the first vertex outside `<w>`, the term

```text
a x_0 a^(-1)                                          (NCP3)
```

lies in the reduced `A_0-M_0-A_0` summand.  No other term in
`a x a^(-1)` has such a component, and an element `y in M` has no reduced
length-three component.  Equality `(NCH2)` therefore forces `x_0=0`, so
`x in D`.

Now `y=a x a^(-1)` belongs both to the first vertex algebra `A` and to `M`.
The normal form gives

```text
A intersect M=D,                                      (NCP4)
```

and hence `y in D`.  This proves `(NCH3)`.  Conjugating the entire equation
by the inverse transporter of one chart gives the two-chart formulation.
