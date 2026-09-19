---
rg: 2
id: binary-leavitt-three-row-compiler-needs-null-prototypes
kind: claim
title: The three-row compiler needs an explicit null-prototype hypothesis
distinct_from:
  binary-leavitt-three-row-atomic-compiler: that is the intended open construction; this audits a missing hypothesis in its literal statement and gives a trivial realization when prototypes are allowed to be arbitrary words.
  atomic-three-row-compiler-is-prototype-gap-equivalent: that identifies the quantitative content after a prototype list has been fixed; this shows why requiring fixed relator fillings is indispensable before the compiler can imply anything about presentation defect.
artifacts:
  - research/binary-leavitt-null-prototype-necessity-proof.md
---

**ESTABLISHED FORMULATION AUDIT AND REPAIR.**  Before this audit, the literal
statement of `binary-leavitt-three-row-atomic-compiler` called the words
`q_j` prototype discrepancies but did not require them to represent the
identity in the presented group or to have fixed fillings by the defining
relators.  Without that requirement, the displayed condition `(BAC1)` is
automatic and has no collapse consequence.

Indeed, take the sole prototype to be the marked word

```text
q_1=z=x_13(s_1t_1).
```

For every sufficiently accurate tuple whose rounded nontrivial spectral
projection `p_U` is nonzero, take the empty address, the empty coefficient
window, and

```text
s_0=s_1=t_0=t_1=0 in p_U M_d(C) p_U.                  (NPT1)
```

All three requested defects are exactly one.  Spectral rounding gives

```text
||z(U)-1||_op>=1                                      (NPT2)
```

once the tuple is sufficiently accurate, so `(BAC1)` holds with `C=1`.
The sole check is its own empty-address conjugate.

This does not instantiate
`bounded-prototype-rows-imply-atomic-morita-return`, whose hypothesis
explicitly requires every prototype to lie in the normal closure of the
defining relators.  Nor does it justify the sentence in
`binary-leavitt-atomic-return-via-three-row-compiler` assigning a fixed
relator filling to every prototype.

Therefore the meaningful open compiler must explicitly require

```text
q_j in <<R>>   for every j,                            (NPT3)
```

or, equivalently for the quantitative application, supply one fixed
relator filling and area bound for each `q_j`.  With `(NPT3)` inserted, the
open burden is exactly the finite prototype gap isolated by
`atomic-three-row-compiler-is-prototype-gap-equivalent`.  Without `(NPT3)`,
the literal compiler is already satisfied but cannot feed the claimed
downstream route.  The compiler node has now been repaired by inserting
`(NPT3)` and fixed fillings into its statement, so this trivial realization
no longer establishes that node and the downstream route is fenced from it.
