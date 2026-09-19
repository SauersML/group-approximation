---
rg: 2
id: two-affine-half-rows-pay-deleted-dyadic-atom
kind: claim
title: Two affine Pauli half rows must pay the deleted dyadic atom
distinct_from:
  affine-reflection-normalizers-have-quarter-overlap: that gives the regular quarter-overlap model for arbitrary affine reflection rows; this computes the exact three-row defect ledger after deleting one deepest dyadic atom from the target.
  dyadic-pauli-payload-flags-supply-strict-target-capacity: that names the source half and strict target complement and uses an abstract capacity inequality; this identifies the unavoidable defect channel for every Pauli/Clifford normalizer implementation of the two rows.
  rectangular-three-row-cell-forces-double-target-capacity: that applies to arbitrary rectangular contractions; this uses the affine-hyperplane geometry of packet-normalizer ranges and obtains the sharper deleted-atom floor.
  finite-packet-flow-keeps-payload-orientation-balanced: that constructs a stationary regular type flow for finite packet diagrams; this is a pointwise two-row calculation on one payload atom and needs no global flow model.
---

**ESTABLISHED AFFINE-NORMALIZER FENCE.**  Fix `n>=1`.  On a payload
projection `C`, let a corrected `n`-qubit Pauli flag packet have its uniform
joint atom decomposition

```text
C=sum_(omega in F_2^n) D_omega,
tau(D_omega)=2^(-n)tau(C).                              (AHR1)
```

Choose one atom `D=D_(omega_*)`, put

```text
E=C(1-Z_1)/2,                 F=C-D,                    (AHR2)
```

and let `U_0,U_1` be packet normalizers which preserve `C`.  Assume their
conjugated source halves

```text
P_i=U_i E U_i^*<=C                                             (AHR3)
```

belong to the affine flag algebra.  Equivalently, each `P_i` is an affine
hyperplane in the `2^n` joint atoms.  Define the most favorable compressed
row maps available from those normalizers,

```text
s_i=F U_i E,                  t_i=s_i^*.                (AHR4)
```

Then the two diagonal-return defects and the crossed-zero defect obey the
exact floor

```text
sum_(i=0)^1 ||t_i s_i-E||_2^2+||t_0s_1||_2^2
 >=tau(D)=2^(-n)tau(C).                                 (AHR5)
```

In particular no pair of payload-preserving Pauli, Clifford, affine-HNN, or
finite flag-normalizer words can synchronize the two inverse rows and one
crossed-zero row through the strict pair `(E,F)` on positive payload mass.
The obstruction does not shrink with matrix dimension.  After exactifying a
fixed approximate packet/normalizer table, `(AHR5)` retains an
`O_n(sqrt(E_pres))` perturbation, so the same conclusion holds for canonical
normalized-HS microstates.

## Proof

All flag projections commute.  Since `U_i` normalizes the flag algebra,
`U_i^*DU_i` commutes with `E`.  Hence

```text
||t_i s_i-E||_2^2=tau(DP_i).                            (AHR6)
```

The final projections of `s_i` are `FP_i`.  Tracial cyclicity therefore gives

```text
||t_0s_1||_2^2=tau(FP_0P_1).                           (AHR7)
```

It remains only to inspect two affine hyperplanes in `F_2^n`.  If they are
equal, their intersection has mass `tau(C)/2`.  If they are complementary,
their intersection is empty and the distinguished atom `D` lies in exactly
one of them.  If they have different linear parts, their intersection has
mass `tau(C)/4`.  In the last case deleting `D` removes at most `tau(D)` from
the intersection, and each occurrence of `D` in a hyperplane is added back
by the corresponding term in `(AHR6)`.  Thus in every case

```text
tau(FP_0P_1)+tau(DP_0)+tau(DP_1)>=tau(D),              (AHR8)
```

where for `n>=2` one uses `tau(D)<=tau(C)/4`; the `n=1` case has only the
equal/complementary alternatives.  Equations `(AHR6)--(AHR8)` prove
`(AHR5)`.

## Consequence for the open compiler

The dyadic target deficit is not merely unavailable from one badly chosen
Clifford routing.  Every finite construction in which the two Leavitt
occurrences act on the flags only through affine normalizers pays precisely
one of two visible quantities: overlap of the two target halves away from
`D`, or loss of a diagonal inverse on `D`.  Adding more flag bits only changes
the floor to the already named mass `2^(-n)tau(C)`.

Therefore the surviving occurrence-synchronization theorem must make at
least one row genuinely nonnormalizing on the flag algebra.  A native
opposite-root/Whitehead coefficient occurrence is not excluded, but it must
couple its non-semisimple coefficient map to the same payload `C`; replacing
that map by a finite Clifford, affine HNN, character transport, or another
normalizer whose image of `E` is an affine flag hyperplane returns to
`(AHR5)`.

DERIVATION
two-affine-half-deleted-atom-proof
