---
rg: 2
id: binary-jacobson-balanced-shift-xor-proof
kind: route
title: Multiply the two-by-two lift and read its action on row roots
target: binary-jacobson-balanced-shift-transport-is-xor
requires:
  - binary-jacobson-monomial-symbol-preimage-is-marked-mf
---

The relations `TS=1`, `Q^2=Q`, `QS=0` and `TQ=0` show directly that the two
matrices in `(JXT1)` are inverses.  The lift is elementary, not merely
invertible.  In characteristic two,

```text
e_12(S)e_21(T)e_12(S)=[[Q,S],[T,0]],
e_12(1)e_21(1)e_12(1)=[[0,1],[1,0]],                   (0)
```

and the product of the two matrices in `(0)` is `a`.  Modulo the finitary
ideal its symbol is `diag(z,z^(-1))`, so `a` lies in the preimage `K` used by
the prerequisite.

Conjugating a column elementary matrix by the two-by-two block `a` multiplies
its coefficient column on the left by `a`.  The two columns of `a` give the
two formulas `(JXT2)`.  Conjugating a row elementary matrix multiplies its
coefficient row on the right by `a^(-1)`; its two rows give `(JXT3)`.  Roots
in distinct rows and one common column, or in one common row and distinct
columns, commute, so the displayed products require no correction term.

Taking `r=1` gives `(JXT4)`.  For commuting involutions `u,v`, simultaneous
spectral decomposition gives

```text
p_(uv)=p_u+p_v-2p_up_v=p_u triangle p_v.               (1)
```

Apply `(1)` to the two factors of `(JXT4)` and conjugate the left spectral
projection by `rho(a)`.  This proves `(JXT5)`; taking coordinate ranks proves
`(JXT6)`.
