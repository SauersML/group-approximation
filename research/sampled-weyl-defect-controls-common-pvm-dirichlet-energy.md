---
rg: 2
id: sampled-weyl-defect-controls-common-pvm-dirichlet-energy
kind: claim
title: Make sparse Weyl defects control transport energy of one common spectral PVM
distinct_from:
  two-matching-matrix-block-propagation: that asks for robust propagation through individual alternating matrix bridges; this asks only for the summed PVM transport energy needed by the scalar expander endpoint.
  same-orbit-closure: that concerns the affine-Leavitt paired-label decoder rather than the sparse Weyl occurrence compiler.
---

OPEN.  After same-basis rounding, let `(P_v)_(v in Omega_n)` be the spectral
PVM on the marked carrier.  Choose a bounded-degree family of sampled mixed
Weyl tests whose induced label transports generate a graph `G_n` with
uniform spectral gap and

```text
|Omega_n| >= 2^(c n).                                         (SW1)
```

Prove that mixed-test defect `epsilon` supplies unitaries `W_s` on the
**same Hilbert space and the same PVM** such that

```text
(1/D) sum_s sum_v ||W_s P_v W_s^*-P_(s v)||_2^2
 <= C epsilon^theta                                            (SW2)
```

for fixed `C,theta>0`, independent of `n` and matrix dimension.

Together with `expander-pvm-transport-forces-dimension-or-mass-collapse`,
this gives

```text
d >= 2^(c n-1)       or       marked mass <= C' epsilon^theta,
```

which is exactly the dimension-witness/mass-collapse alternative required
by the occurrence compiler.

The abstract exact two-field-matching closure is already established by
`two-untwisted-field-matchings-force-complete-cross-commutation`; the open
content is the normalized-HS conversion from sparse sampled commutators to
the *summed* transport estimate `(SW2)`.

## Attempts

- **Propagate one matrix bridge.**  The local bridge estimate is quadratic
  in the bridge amplitude, so iteration loses tiny blocks.
- **Use only dimension expansion of the linear maps.**  Rank/support
  expansion gives no Poincare estimate for a weighted approximate model.
  The needed hypothesis is spectral expansion of the induced transport
  graph, together with `(SW2)`.
- **Compare context PVMs separately.**  This permits incompatible couplings
  and rectangular/multiplicity escape.  The estimate must concern one
  common PVM on one Hilbert space.

