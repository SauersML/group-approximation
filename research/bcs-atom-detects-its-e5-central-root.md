---
rg: 2
id: bcs-atom-detects-its-e5-central-root
kind: claim
title: A selected BCS atom has positive mass on its E5 central-root support
distinct_from:
  hs-steinberg-morita-trace-additivity-on-adaptive-blocks: That asks for one globally compatible additive mass on the whole bounded adaptive tree; this is the local payload-to-root support estimate at one named source idempotent.
  e5-idempotent-root-has-two-pair-extraspecial-cell: That uniformly splits mass already lying in a nontrivial central-root sector; this must put the actual BCS atom into that sector.
  marked-hs-separation-forces-spectral-density: That lower-bounds spectral density from displacement of the root word itself; this must lower-bound the root displacement/support on the particular BCS projection.
  hs-steinberg-bcs-corner-kernel-is-linear-sofic: That reconstructs a rank-metric model of the whole conditional coefficient quotient; this asks only for one overlap inequality on the finite adaptive menu.
---

**OPEN PAYLOAD-TO-ROOT INTERFACE.**  In a normalized-HS microstate of the
rank-five wordization of `finite-adaptive-selected-atom-ring-tree`, fix one
node and forbidden type and write

```text
E=Q_sigma P_i,              a=a_(sigma,i),
Z=x_13(a),
S_Z=1-P_(Z,1),                                      (BZR1)
```

where `E` is formed from the rounded shared BCS tuple and `P_(Z,1)` is the
`1`-eigenspace projection of the exactified order-`p` root word `Z`.
Prove, with constants independent of matrix dimension,

```text
tr(E S_Z)>=c_root tr(E)-C sqrt(E_pres),                (BZR2)
```

for one fixed `c_root>0`.  The same estimate is required only for the finite
menu of sources up to the chosen contradiction depth.

The algebraic transverse packet is already present.  By
`e5-idempotent-root-has-two-pair-extraspecial-cell`, the four canonical
roots with coefficient `a` form two Heisenberg pairs centered at `Z`.  Once
`E S_Z` approximately reduces that fixed packet, finite Stone--von Neumann
gives a joint spectator atom of mass

```text
p^(-2) tr(E S_Z).                                     (BZR3)
```

Thus `(BZR2)` supplies the conditioned-source mass which the bare additive
table lacks.

This claim is not a consequence of root spectral density alone.  The group
microstate is an abstract unitary representation of the Steinberg
wordization, not the canonical elementary-matrix representation of the
coefficient star algebra.  Root relations make the common root kernel a
two-sided coefficient ideal, but they do not presently reflect the
operator-valued BCS projection into the complement of that kernel.  Proving
that reflection is the local finite-menu version of the metric decoder.

The most direct multiplicative-covariance proof is now ruled out exactly.
`root-scaling-covariance-does-not-detect-bcs-atom` observes that the
relations obtained from `u_j a=plus_or_minus a` admit a one-dimensional
marked representation with the prescribed BCS joint character and with the
entire root packet trivial.  Thus conjugation of `Z` by the assignment
involutions, even together with the two transverse Heisenberg pairs, cannot
imply `(BZR2)`.  A successful estimate must use a mixed row which prevents
the coefficient `a` from entering the root kernel on the physical BCS
carrier.

Even `(BZR2)` is not by itself the final theorem: the edgewise oriented
tables must still assign one common mass to the same parent carrier across
all outgoing types.  It separates the two remaining issues cleanly:

```text
payload-to-root detection,       then       global common orientation.
```
