---
rg: 2
id: verifier-controlled-two-cycle-is-existentially-loss-blind
kind: claim
title: A verifier-controlled two-cycle localizes one losing projection but cannot charge for its mass
distinct_from:
  central-marked-two-cycle-zero-compression-cell: that constructs and robustly estimates the selected zero-compression cell; this proves that feeding the verifier reflection into its marked grading makes the cell exactly completable at every losing mass.
  one-round-v4-lamps-wordize-a-bcs-losing-projection: that wordizes one BCS losing reflection in an intended lamp representation; this audits what happens after such a reflection has already been obtained as one ordinary word.
  existential-fock-library-has-zero-carrier-or-regular-firewall: that treats an arbitrary existential challenge library; this gives the explicit two-dimensional controlled-swap completion for the proposed k=1 cell.
---

**ESTABLISHED.**  Suppose an ordinary group word `r` has already been made a
self-adjoint involution and, in an intended verifier representation, satisfies

```text
r=1-2L                                                   (VTL1)
```

for a BCS losing projection `L`.  Adjoin involutions `z,w` with

```text
[r,z]=[r,w]=1,                 w z w^-1=r z.             (VTL2)
```

Then the selected atom

```text
q=(1-r)(1-z)/4                                         (VTL3)
```

is `L(1-z)/2`, and `q w q=0`.  Thus, **conditionally on wordizing the
verifier reflection**, an arbitrary fixed forbidden projection really does
reduce to one zero-compression payload.

This reduction does not pay for losing mass.  For every self-adjoint
involution `R` on every Hilbert space, irrespective of the trace of its
negative spectral projection, `(VTL2)` has an exact two-dimensional
extension.  Put

```text
E_-=(1-R)/2,       E_+=(1+R)/2,
z=1 tensor Z,      w=E_+ tensor 1+E_- tensor X.          (VTL4)
```

Then all relations `(VTL2)` hold exactly and

```text
q=E_- tensor (1-Z)/2,             q w q=0.               (VTL5)
```

Consequently the optimized residual of this existential cell is zero for
every verifier reflection, even when `tau(L)` is bounded below.  Approximate
involutions give approximate extensions after the standard spectral rounding,
with loss tending to zero with the original involution defect.  Hence this
cell cannot establish an estimate of the form

```text
beta tau(L) <= C Def_relations^2                           (VTL6)
```

for any `beta>0`.

The exact remaining gate is therefore not `k=1` localization.  It is a
**noncompletable payment cell**: an ordinary-word relation whose optimized
finite-dimensional defect is bounded below by the losing mass, while the
common perfect infinite verifier still has one exact marked completion.

