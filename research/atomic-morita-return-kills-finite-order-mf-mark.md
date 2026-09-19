---
rg: 2
id: atomic-morita-return-kills-finite-order-mf-mark
kind: claim
title: Atomic Morita Return kills a finite-order mark in every norm matrix corona
distinct_from:
  authenticated-coarse-fine-return-forces-mf-collapse: that exactifies depth-one and depth-two matrix-unit packets on one carrier and uses one rank-deficient return row; this returns four coefficient operators to a prescribed spectral atom and uses three approximate Leavitt rows.
  compression-defect-dies-in-mf-under-mark-stability: that assumes global point-norm stability and repairs the whole almost representation; this assumes only a local coefficient return on one nonzero spectral atom and repairs no representation.
  torsion-normal-generator-mf-shadow-equivalence: that converts operator-to-Hilbert--Schmidt invisibility on a torsion normal generator; this stays entirely in operator norm and needs no positive-density active core.
artifacts:
  - research/atomic-morita-return-collapse-proof.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**ESTABLISHED CONDITIONAL COLLAPSE THEOREM.** Let
`Gamma=<S|R>` be finitely presented and let `w` be a finite-order marked
word.  Say that `(Gamma,w)` has **binary Atomic Morita Return (AMR)** if
there is a modulus `eta(delta)->0` such that the following holds.

Spectrally round `w(U)` in every sufficiently accurate finite-dimensional
unitary presentation model `U`.  For every nontrivial spectral value and its
prescribed rounded spectral projection `p_U`, whenever `p_U!=0` there are
bounded operators

```text
s_0,s_1,t_0,t_1 in p_U M_d(C) p_U
```

with

```text
||t_i s_i-p_U||_op <= eta(delta),              i=0,1,
||s_0t_0+s_1t_1-p_U||_op <= eta(delta).                (AMR1)
```

Then

```text
w in Rad_MF(Gamma).                                    (AMR2)
```

If `<<w>>_Gamma=Gamma`, then

```text
Rad_MF(Gamma)=Gamma.                                   (AMR3)
```

No positive lower bound on `rank(p_U)/d`, off-diagonal Leavitt relation,
trace estimate in the ambient normalized trace, property `(T)`, stability
hypothesis, or common carrier across different coordinates is required.  A
different finite coefficient window may be used at every coordinate: only
the three rows on the prescribed nonzero atom at that coordinate matter.

