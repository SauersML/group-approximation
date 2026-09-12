---
rg: 2
id: leavitt-normal-root-square-equation-has-amalgam-countermodel
kind: claim
title: The degree-two equation built from a normally generating Leavitt root has an explicit nonsolvable amalgam countermodel
distinct_from:
  leavitt-degree-kernel-quotient-tests-are-procyclic: That proves abstractly that any obstruction quotient must be infinite perfect and finite-quotient-free; this identifies such a quotient exactly for one concrete word built from a normal generator.
  leavitt-degree-kernel-normally-generated-by-one-word: That asks for a word whose ambient normal closure is the whole degree kernel; this proves that the most direct word made from a normally generating coefficient does not work.
  full-leavitt-idempotent-defect-saturation: That proves one Leavitt root normally generates a Steinberg group and its elementary quotient; this shows why putting that root next to the nonsingular power of the variable still does not normally generate the degree kernel.
  kl-simple-failure-leaves-only-the-cyclic-quotient: That describes what every violation over a simple group would force; this is a concrete noncyclic quotient showing that one natural candidate is not a violation.
---

Let `G=L_(F_2)(1,2)^x`.  Via the rank-twenty equivalence
`G ~= EL_20(R)`, let `r in G` be the image of the explicit nonzero elementary
root `x_13(q)` from `full-leavitt-idempotent-defect-saturation`.  Then

```text
r^2=1,       r!=1,       <<r>>_G=G.                       (LRS1)
```

The concrete degree-two word

```text
w=r t^2 in G*<t>
```

does **not** normally generate `N_2=ker(G*<t>->C_2)`.  In fact

```text
(G*<t>)/<<r t^2>>  ~=  G *_(<r>=<t^2>) C_4,              (LRS2)
```

so the coefficient copy of `G` embeds.  More sharply, if

```text
Q_w=N_2/<<w>>_(G*<t>),
```

then

```text
Q_w ~= G *_<r> G.                                        (LRS3)
```

This is the explicit infinite perfect, no-finite-quotient obstruction predicted
by `leavitt-degree-kernel-quotient-tests-are-procyclic`.

Thus normal generation of the coefficient `r` inside `G` is not enough:
the equation identifies `r` with the square of the new stable letter instead
of killing it, and all ambient conjugates preserve that identification.  A
viable candidate must couple at least two separated variable blocks to
different coefficient conjugacy data; a single normally generating root next
to `t^m` can never exploit simplicity or root saturation.

