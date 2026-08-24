---
rg: 2
id: agent-aggregate-escape-trivial-root-substitution-proof
kind: route
title: Substitute the boundedly trivial word in every mixed relator
target: agent-aggregate-escape-trivial-root-erases-mixed-rows
requires:
  - agent-free-compressor-padded-j-row-kills-payload-root
---

Because `w=1` follows from `R`, adding `r_j(S,Y,w)` or
`r_j(S,Y,1)` gives the same normal closure over `R`; this proves `(BTR2)`.

For the metric statement, a derivation

```text
w=product_(ell=1)^D c_ell r_(i_ell)^(epsilon_ell) c_ell^(-1)
```

and unitary invariance give `(BTR3)` by telescoping.  Replace the occurrences
of `w^(plus_or_minus 1)` in `r_j` one at a time.  Each replacement changes
the represented unitary by at most `||rho(w)-1||_2`, since
`||rho(w)^(-1)-1||_2=||rho(w)-1||_2`.  A second telescoping proves `(BTR4)`.

If the residual presentation has a forbidden-mass representation, `(BTR2)`
extends it to the original mixed presentation and `w=1`, contradicting
`(BTR5)` at zero energy.  Otherwise its residual rows, not the deleted root,
are what remove forbidden mass.  This proves the dichotomy.
