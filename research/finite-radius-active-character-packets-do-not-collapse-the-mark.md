---
rg: 2
id: finite-radius-active-character-packets-do-not-collapse-the-mark
kind: claim
title: Finite-radius active-character PVMs retain the canonical mark and move all failure into actor loops
distinct_from:
  affine-leavitt-global-root-pvm-collapses-active-mark: that uses one finite-support PVM for the entire infinite module and sums the full Schreier boundary; this shows why a fixed finite-radius PVM is insufficient.
  rectangular-escape: that enlarges paired label quotients while shrinking multiplicity; this is a simpler regular-PVM countermodel for arbitrary finite collections of partial linear actor maps.
  affine-leavitt-boundary-shear-payment: that may use mixed Steinberg loop words to charge the boundary; this proves that character PVMs and local edge covariance alone cannot supply that charge.
---

ESTABLISHED.  Let `W` be a nonzero finite-dimensional vector space over
`F_p`.  Let

```text
theta_a:V_a -> V'_a       (a in Q)                          (FRC1)
```

be any finite family of linear isomorphisms between equal-dimensional
subspaces of `W`.  There is a finite-dimensional exact representation
`rho:W->U(H)` and unitaries `U_a` such that

```text
tr(rho(w))=0                         for every 0!=w in W,
U_a rho(v) U_a^*=rho(theta_a(v))     for every v in V_a.    (FRC2)
```

Namely take the regular character PVM on `H=ell^2(W_hat)`.  Extend each
partial isomorphism `theta_a` arbitrarily to `T_a in GL(W)` and let `U_a`
be the dual permutation unitary.

Apply this to any fixed-radius affine-Leavitt active-root window: take `W`
to contain the finitely many last-column coefficients in the window, and
take `(FRC1)` to be every actor transport whose source and target have been
included.  Then all finite additive tables, all canonical module trace
tests, and all listed local actor covariance tests hold **exactly**, while

```text
||rho(x_16(A))-I||_2^2=2.                                  (FRC3)
```

Thus the active-character orbit gap alone cannot yield a fixed-depth bound

```text
||x_16(A)-I||_2^2 <= b_N+C_N error,       b_N->0,           (FRC4)
```

from only the radius-`N` additive PVM and edge-covariance data.

The arbitrary extensions `T_a` generally do not satisfy the Steinberg
actor relators jointly.  More precisely, the failing words are actor
relator loops and mixed covariance loops whose intermediate coefficient
subspaces leave the chosen window.  If all such loops were exact on one
finite model, its PVM support would be a finite actor-invariant character
set, contradicting
`affine-leavitt-active-root-character-orbits-are-aperiodic` whenever the
active mark survives.

Consequently there are only two viable uses of the character backend:

1. decode one **global** whole-module PVM and control its full actor energy;
2. add a genuinely new mixed-word boundary estimate which charges the
   failure of the extensions around the actor loops.

The second option is the old `affine-leavitt-boundary-shear-payment`
problem in new language.  Finite radius by itself is not a bypass.
