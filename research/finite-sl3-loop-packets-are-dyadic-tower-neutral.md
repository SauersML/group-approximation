---
rg: 2
id: finite-sl3-loop-packets-are-dyadic-tower-neutral
kind: claim
title: Every finite packet of lattice-only SL3 loops is neutral on the all-depth dyadic lamp tower
invalidates:
  - sl3-dyadic-tower-exclusion-from-six-a2-loops
artifacts:
  - research/finite-sl3-loop-dyadic-tower-model-proof.md
distinct_from:
  finite-lamp-frame-is-matrix-range-neutral: that separates an arbitrary fixed word window for freely chosen conjugators; this keeps one genuine finite quotient of the lattice actor, exact covariance on the complete finite orbit of the denominator coset, and then diagonalizes to all dyadic depths.
  one-steinberg-loop-is-hnn-gram-neutral: that observes one relation gives two names for one coset endpoint at the scalar Gram level; this constructs exact finite models satisfying every lattice relation, all six noncommuting A2 loops, and the full nested dyadic PVM tower on the finite orbit.
  six-chamber-a2-holonomy-closes-fixed-clock-sector: that kills an external corrector after a common finite Chevalley root packet and a coweight triangle have been recovered; this shows that the six lattice loops alone do not recover such a packet from covariant dyadic lamp atoms.
---

Put

```text
C=SL_3(Z),                  h=diag(2,1,1/2),
C_0=C intersect hCh^(-1),  X=C/C_0.                         (FLP1)
```

The left `C`-orbit of `hC` in `A/C`, for `A=SL_3(Z[1/2])`, is the finite
set `X`.  More generally, every `a in A` commensurates `C`, so every
`C`-orbit in `A/C` is finite; a finite loop packet lies in a finite union of
such orbits.  The following construction applies verbatim to that finite
union.  For every depth `R` and every finite set `Omega` of nonidentity
reduced lamp/actor words there is an exact finite-dimensional model with:

1. one order-`2^R` lamp `z_x` for every `x in X`;
2. exact covariance `c z_x c^(-1)=z_(cx)` through the finite permutation
   quotient of `C` on `X`;
3. a nested dyadic spectral PVM

   ```text
   q_(r,j)^x,      1<=r<=R, 0<=j<2^r,                       (FLP2)
   ```

   with trace `2^(-r)` and the refinement law `(DPT2)`; and
4. canonical trace zero for every word in `Omega`.

One obtains the model from a finite regular quotient of

```text
K_R=(*_(x in X) C_(2^R,x)) semidirect F,                    (FLP3)
```

where `F` is the finite image of `C` in `Sym(X)`.  The group `K_R` is
virtually free and residually finite.  Residual finiteness preserves the
required word window, the actor `F`, and every nontrivial power of every
lamp.  In the finite regular representation, exact lamp order gives uniform
`2^R`-point spectrum and hence `(FLP2)`.

Letting `R` and the word window tend to infinity yields a tracial matrix
ultraproduct containing the entire nested dyadic tower on `X`.  Its lamp
algebras are freely independent, covariance by the lattice actor is exact,
and **every** relation of `C` holds.  In particular all six noncommuting
rank-two relations

```text
[x_12(s),x_23(t)]=x_13(st),  [x_21(s),x_13(t)]=x_23(st),
[x_23(s),x_31(t)]=x_21(st),  [x_32(s),x_21(t)]=x_31(st),
[x_31(s),x_12(t)]=x_32(st),  [x_13(s),x_32(t)]=x_12(st)       (FLP4)
```

close on the same physical atoms at every depth.

Therefore no finite set of loops contained entirely in `C`, even the whole
six-chamber `A_2` packet, can by itself force a dimension or rank
contradiction from `(DPT2)--(DPT5)`.  This does not refute
`sl3-outliers-have-no-dyadic-a2-pvm-tower`: each model covers only finitely
many finite `C`-orbits and does not extend the actor from `C` to `A`.  It
sharpens the residual.  Any successful loop packet must cross a
denominator edge, compare two different `C`-orbits in `A/C`, or use the
uniform ambient-extension outlier quantitatively; lattice holonomy alone is
neutral.

DERIVATION
finite-sl3-loop-dyadic-tower-model-proof
