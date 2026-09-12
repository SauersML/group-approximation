---
rg: 2
id: gauge-optimized-target-has-uniform-congruence-tangent-gap
kind: claim
title: The gauge-optimized target has no moving-level infinitesimal obstruction
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that proves the Mayer--Vietoris cocycle gap in two modular-vertex coordinates; this transfers it to the exact-core-optimized induced target and identifies what a failure of the nonlinear estimate would have to look like.
  gauge-optimized-induced-energy-target: that states the global finite-dimensional energy estimate needed for flexible repair; this proves only its first-order congruence-point analogue.
  normalized-hs-taylor-remainder-is-not-dimension-free: that refutes integration of a tangent gap by an HS Taylor estimate; this confirms the tangent gap and therefore localizes the surviving obstruction to precisely that nonlinear integration step.
---

Let `rho_N` be any exact congruence endpoint and write the Iwahori
presentation as two modular vertices glued over their common BS/Iwahori
core.  Restrict to the **locally exact tangent slice**: infinitesimal
perturbations which are cocycles on each modular vertex separately.  Let
`Z_N` be the tangent space to the compatible global endpoint locus, and let
`dF_N` be the linearized edge mismatch.  There is one constant `sigma>0`,
independent of `N`, the congruence representation, its dimension, and its
multiplicity, such that

```text
dist_2(v,Z_N) <= sigma^(-1)||dF_N(v)||_2.              (GIT1)
```

In the square-free coordinates `(X,R,T)` of
`gauge-optimized-induced-energy-target`, `(GIT1)` is exactly the linear
coercivity statement obtained after quotienting the induced edge defect by
all tangent motions of the exact core variety `C_N(d)`.  Thus the corrected
gauge-optimized target has no sequence of congruence-point tangent modes
whose inverse constant diverges with the dyadic level.

Consequently any failure of the global estimate `(GOI5)` must be genuinely
nonlinear.  It must use at least one of:

```text
operator-large motion on a small HS carrier,
torsion-multiplicity/rank changes,
or motion outside every uniform coordinate tube of the exact endpoint locus.
                                                               (GIT2)
```

The scalar `r`-character firewall is not such a tangent obstruction: after
the exact-core direction is included it is one of the quotient directions
removed in `(GIT1)`.

## Proof

`iwahori-uniform-infinitesimal-rigidity` proves `(GIT1)` in modular-vertex
cocycle coordinates, with a constant independent of the congruence level
and coefficient representation.  The reversible change between those
coordinates and the square-free `(X,R,T)` coordinates uses a fixed finite
list of group words.  Its differential and inverse differential are sums
of a fixed number of unitary left-right multiplications, hence their
operator norms on normalized Hilbert--Schmidt cochains are bounded by
universal constants.  It therefore transports `(GIT1)` with only a fixed
change of `sigma`.

On the locally exact tangent slice, changing the chosen exact core is
precisely adding a tangent vector to `C_N(d)`.  Compatible vertex cocycle
pairs are precisely the tangent vectors of a global exact endpoint.  Hence
the quotient by core changes in the linearization of `(GOI4)` is the same
Mayer--Vietoris quotient controlled by `(GIT1)`.

Finally, if a small-amplitude tangent countersequence to `(GOI5)` existed,
rescaling it to unit tangent norm would contradict `(GIT1)`.  The remaining
possibilities are therefore nonlinear and are exactly the mechanisms in
`(GIT2)`.  This last conclusion does not integrate `(GIT1)` in normalized
HS: `normalized-hs-taylor-remainder-is-not-dimension-free` shows why that
integration is still unavailable.

## Consequence for the next attack

Further projective-line section optimization cannot reveal a missing
linear spectral gap: that gap is already present after the correct gauge
quotient.  The next useful theorem must be a nonlinear truncation/dilation
or coordinate-basin result which pays the operator-large carrier by its
rank and then applies `(GIT1)` on the remaining operator-small carrier.
