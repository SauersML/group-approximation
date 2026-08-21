---
rg: 2
id: sampled-weyl-defect-controls-common-pvm-dirichlet-energy
kind: claim
title: Make sparse Weyl defects control transport energy of one common spectral PVM
distinct_from:
  two-matching-matrix-block-propagation: that asks for robust propagation through individual alternating matrix bridges; this asks only for the summed PVM transport energy needed by the scalar expander endpoint.
  same-orbit-closure: that concerns the affine-Leavitt paired-label decoder rather than the sparse Weyl occurrence compiler.
---

OPEN.  After same-basis rounding, let `U,W:F_2^n->U(H)` be the two exact
additive actions on the marked carrier.  For the two field matchings

```text
a=b,                         a=alpha b,
```

prove the dimension-independent RMS closure estimate

```text
(E_(a,b) ||U(a)W(b)-(-1)^<a,b>W(b)U(a)||_2^2)^(1/2)
 <= C epsilon^theta,                                          (SW0)
```

where `epsilon` is the larger RMS defect on the two sampled matchings and
`C,theta>0` are independent of `n` and matrix dimension.

By `full-weyl-defect-equals-pvm-transport-energy`, `(SW0)` is **equivalent**
to controlling the complete-translation transport energy of the spectral
PVM `(P_v)`:

```text
|Omega_n| >= 2^(c n).                                         (SW1)
```

```text
(1/2^n) sum_b sum_v ||W(b) P_v W(b)^*-P_(v+b)||_2^2
 <= C epsilon^theta                                            (SW2)
```

for fixed `C,theta>0`, independent of `n` and matrix dimension.

Together with the Parseval identity and
`expander-pvm-transport-forces-dimension-or-mass-collapse`,
this gives

```text
d >= 2^(c n-1)       or       marked mass <= C' epsilon^theta,
```

which is exactly the dimension-witness/mass-collapse alternative required
by the occurrence compiler.

The abstract exact two-field-matching closure (the zero-defect case of
`(SW0)`) is already established by
`two-untwisted-field-matchings-force-complete-cross-commutation`; the open
content is its rank-independent quantitative stability.  The current
centralizer-fiber circuit proves `(SW0)` only with a factor
`K_n=O(n^(1+log_2 3))`.

The most direct scalar counterrepresentation lane is also closed.
`phased-translations-reduce-to-alpha-plane-test` considers every table obtained
by conjugating the regular translation action by an arbitrary diagonal Boolean
phase.  Kaufman--Sudan single-orbit soundness gives the dimension-free squared
HS estimate `full defect <=(27/2) sampled defect` for this entire family.
Thus any obstruction to `(SW0)` must use genuinely operator-valued mixing, not
one scalar phase orbit.

`matrix-phased-translations-exact-identity-scalarize` extends that conclusion
to arbitrary block-diagonal matrix phases when the identity matching is exact:
the blocks become commuting reflections and `(SW0)` holds with squared-energy
constant `27/2`.  The same node explains why near-identity rounding cannot be
performed before using the alpha constraint: sparse Pauli anticommutation
graphs obstruct a uniform standalone simultaneous-diagonalization lemma.

## Attempts

- **Propagate one matrix bridge.**  The local bridge estimate is quadratic
  in the bridge amplitude, so iteration loses tiny blocks.
- **Use only dimension expansion of the linear maps.**  Rank/support
  expansion gives no rank-independent closure estimate.  Parseval shows
  that the desired endpoint is already the full average defect `(SW0)`;
  deriving it from two matchings remains a two-dimensional
  curvature/agreement problem, not a one-dimensional Poincare estimate.
- **Compare context PVMs separately.**  This permits incompatible couplings
  and rectangular/multiplicity escape.  The estimate must concern one
  common PVM on one Hilbert space.
