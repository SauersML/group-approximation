---
rg: 2
id: canonical-hnn-flat-boundary-enemy
kind: claim
title: The canonical arithmetic HNN model has an exact flat boundary dilation
distinct_from:
  canonical-exact-polar-models-have-flat-singular-loss: that gives finite-dimensional canonical vertex calibrations but has no projective fold witness; this tensors the regular HNN witness itself and keeps the entire retained group character canonical.
  sl3-regular-double-bass-serre-rigidity-firewall: that exhibits the undilated infinite-dimensional fold enemy; this adds fixed raw boundary leakage while leaving the retained polar group tuple unchanged.
  complement-energy-is-bounded-by-polar-modulus-and-boundary: that forces modulus mismatch or boundary leakage in a nondegenerate polar enemy; this proves that the boundary alternative cannot be charged by any tracial word-moment identity.
---

**ESTABLISHED EXACT ENEMY.**  Put

```text
C=SL_3(Z) < A=SL_3(Z[1/2]),
G=A *_C (C direct_product Z)=<A,t | [t,c]=1 (c in C)>.
```

Fix a finite symmetric packet `S_A` of nonidentity elements and
`0<alpha<1`.  There is an exact representation `Pi:A->U(M)` in a finite
tracial von Neumann algebra, a positive-trace projection `P`, and a unitary
`U in PMP` with the following properties.  If

```text
T_s=P Pi(s) P,       rho_s=polar(T_s),
mu_s=||U|T_s|-|T_s|U||_(2,P)^2,
ell_s=tau(P)^(-1) tau(P Pi(s)^*(1-P)Pi(s)P),             (CHB1)
```

then, for every `s in S_A`,

```text
T_s=alpha rho_s,       mu_s=0,       ell_s=1-alpha^2.    (CHB2)
```

Moreover the corner tuple

```text
a |-> rho_a,          t |-> U                              (CHB3)
```

is exactly the canonical regular representation of `G`.  In particular all
HNN relators have zero defect, every nonidentity group word has normalized
corner trace zero, `U` commutes with `rho(C)`, and for `h in A-C`,

```text
tr_P([U,rho_h])=0.                                      (CHB4)
```

Consequently no inequality valid in arbitrary finite tracial von Neumann
algebras can bound the raw boundary term in `(CHB1)` by the original group
relator defects and finitely or infinitely many canonical word-moment
errors, with a right side vanishing when those errors vanish.  The desired
payment in `sl3-regular-arithmetic-double-fold-mark-collapse` must be
genuinely matricial/Connes-embedding-sensitive; full canonical mixed words
alone do not control the dilation boundary.

This does not provide finite matrix microstates of `G`, and hence does not
refute the arithmetic route.  It rules out only a tracial identity or an
arbitrary-dilation estimate.  A positive proof now has to show that a
vanishing-defect **matrix** tuple admits a specially selected dilation for
which the boundary is controlled; it cannot demand such control for every
exact tracial dilation.

