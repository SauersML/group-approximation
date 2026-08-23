---
rg: 2
id: regular-iwahori-relative-congruence-exactification
kind: claim
title: Regular Iwahori pairs are relatively congruence-exactifiable
distinct_from:
  odd-label-stabilization-has-uniform-repair: that completes repair of an already congruence mixed-CRT pair; this asks to move an arbitrary exact modular-vertex pair into that locus before applying the repair.
  iwahori-outlier-repair: that asks directly for a full-rank compatible correction in the localized sector; this isolates a stronger but sharply arithmetic preprocessing theorem sufficient for it.
  character-rigidity-equals-hyperfinite-hs-stability: that controls hyperfinite character sectors and finite-quotient approximability in a weak sense; this asks for generatorwise normalized-HS proximity to congruence vertex representations.
---

Let `pi_(n,+),pi_(n,-):SL_2(Z)->U(d_n)` be exact vertex
representations with Iwahori defect tending to zero.  Suppose the compatible
homomorphism of `SL_2(Z[1/2])` induced in the matrix ultraproduct has the
regular trace.  Then there are exact, same-dimensional vertex
representations `rho_(n,+),rho_(n,-)`, each factoring through a congruence
quotient, such that

```text
d_2(pi_(n,+),rho_(n,+))+d_2(pi_(n,-),rho_(n,-)) -> 0,   (RCE1)
def(rho_(n,+),rho_(n,-)) -> 0.                          (RCE2)
```

This is the sharp arithmetic theorem still missing after exact congruence
repair.  It is deliberately a *relative* statement: the inputs are already
honest representations of each modular vertex, and only their gluing is
asymptotic.  It asserts neither HS stability of arbitrary approximate
`SL_2(Z)` representations nor a classification of all its finite-dimensional
representations.

The claim is open.  Regular trace alone is insufficient to prove it by
spectral bookkeeping, because
`residual-finite-tensor-camouflages-iwahori-transfer-failures` makes any
tensor-stable edge geometry regular-tracial.  Property `(tau)` supplies the
uniform polar/repair estimate only after `(RCE1)` has placed the vertices in
congruence quotients.  It does not establish `(RCE1)`.

## Attempts

- **Central-regular localization.**
  `iwahori-outlier-localization` reduces a failed sequence to collapsing
  mixed gaps between high-dimensional edge irreducibles.  It removes sparse
  arbitrary operator spaces but retains only extension through `SL_2(Z)`;
  `modular-vertex-extension-does-not-force-congruence` shows why this stops
  short of `(RCE1)`.
- **Character rigidity and canonical trace.**  Peterson--Thom rigidity and
  Dogon--Vigdorovich hyperfinite stability handle the
  finite-character/hyperfinite sectors, but do not give generatorwise
  proximity to a finite quotient in the regular sector.  The tensor theorem
  `residual-finite-tensor-camouflages-iwahori-transfer-failures` makes this
  failure sharp: canonical trace can be imposed without changing the edge
  obstruction.
- **Selberg `(tau)`.**  The uniform congruence spectral gap powers polar and
  rank repair after exactification.  Applying it before `(RCE1)` is circular,
  because an arbitrary modular representation has no congruence quotient
  action on which to average.
- **Alternative direct route.**  `skeleton-relative-hs-stability-for-sl2`
  tries to bypass congruence exactification by repairing an exact parabolic
  skeleton and its Weyl holonomy.  It is a route to the same Iwahori endpoint,
  not an established implication to `(RCE1)`.
