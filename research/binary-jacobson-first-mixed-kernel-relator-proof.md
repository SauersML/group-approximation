---
rg: 2
id: binary-jacobson-first-mixed-kernel-relator-proof
kind: route
title: Reduce the cyclic balanced product in the finite-overlap amalgam
target: binary-jacobson-first-mixed-kernel-is-three-syllable
requires:
  - binary-jacobson-one-step-finite-type-envelope-is-marked-mf
  - binary-jacobson-three-cycle-is-controlled-swap-and-marked-mf
---

The multiplication `(JKR3)` is `(JTCP3)` in
`binary-jacobson-three-cycle-controlled-swap-proof`; it uses

```text
TS=1,    TQ=0,    QS=0,    Q^2=Q,    ST+Q=1.
```

It proves that `(JKR4)` maps to one in `E`.

It remains to audit the word in the abstract envelope.  Since `r^3=1`,
`r^(-2)=r` and `r^(-1)=r^2`.  Expanding `(JKR4)` and collecting only adjacent
`F`-letters gives

```text
r^2 h (u r r) h (u r^2) h u c^(-1)
 =r^2 h (u r^2) h (u r^2) h u c^(-1),
```

which is `(JKR5)`.  The permutation `u` is a transposition and `r^2` is a
three-cycle, hence `k=u r^2` is nonidentity.  In the product decomposition
`F=G_Q x G_P`, a constant matrix has form `(g,g)`, while `(JFT4a)` says every
element of `K` has form `(g,1)`.  Thus a nonidentity constant cannot lie in
`K`.  Both internal `F`-syllables in `(JKR5)` are outside `K`; the three
letters `h` lie in `(K x <h>)\K`.  The normal-form theorem for an amalgamated
free product makes `(JKR5)` nonidentity.

For the lower bound, an amalgam word with at most two `h` occurrences can be
written, after absorbing endpoint elements, in one of the three forms listed
in the claim.  If the two-letter form maps to one, then
`h f_1 h in F`, equivalently `f_1 in F cap hFh=K`; this is exactly an
amalgamating pinch.  Removing it leaves an `F` word, and the vertex embedding
is faithful in both `Gamma_F` and `E`.  This proves optimality.

For the final retraction, the explicit overlap `(JFT4a)` makes
`t=(1,u)` commute with `K`, so the map `h |-> t` respects the amalgam.  The
constant cycle `r` is `(r,r)`, while the constant Weyl word is `u=(u,u)`.
Therefore `hu` maps to `(u,1)`, and

```text
(r^2 u r^(-2))(r u r^(-1))u=w_31 w_23 w_12=w_23
```

in `GL_3(F_2)`.  On the other hand `(JKR3)` evaluates to `w_23` on the
`Q` factor and to the identity on the `P` factor, so `c=(w_23,1)`.  The image
of `R_3` is one, and the resulting quotient map is the identity on `F`, as
claimed.
