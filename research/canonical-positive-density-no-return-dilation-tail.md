---
rg: 2
id: canonical-positive-density-no-return-dilation-tail
kind: claim
title: Attach a no-return dilation tail without diluting the canonical head
distinct_from:
  block-encoded-acceptance-still-needs-corner-return: that produces one unitary whose first compression is the acceptance contraction; this asks for coherent powers of that compression.
  geometric-infinite-counter-is-hs-trace-diluting: that proves the ordinary unilateral/cyclic head has vanishing normalized density; this asks for a packet-authenticated head of fixed canonical density.
  self-similar-cylinder-return-regular-energy-floor: that computes the regular obstruction to returning one self-similar cylinder; this permits no return at all and uses orbit capacity as the contradiction.
---

Given the fresh-control block encoding `W` of a fixed finite-game acceptance
compressor, construct an effective ordinary group extension, a rational
idempotent `q` selecting a positive-Plancherel-mass packet type, and a unitary
word `u` such that the selected and correctly oriented compression is

```text
T=qWq.
```

and, after packet exactification in every canonical-profile matrix
microstate, for every fixed `N`,

```text
q u^n q=T^n+o(1),             0<=n<=N,                 (NRT1)
tr(q)->tau_Gamma(q)>0.                                      (NRT2)
```

The error constants may depend arbitrarily on `N`.  In one exact
properly-infinite completeness representation, the extension must retain the
perfect fixed carrier and keep `q!=0` algebraically.

Equation `(NRT1)` says that amplitude which exits the head after one use of
`W` cannot return to it during the first `N` steps.  The content is not the
existence of a unitary dilation--that is automatic--but authentication of a
single head whose normalized canonical mass does not fall as `N` grows.

## Attempts

- A unilateral level register gives exact no-return powers, but its head has
  density `1/(N+1)` in finite truncations.
- The Pauli zero atom fixes the mass of a correctly oriented control type but
  does not itself select that orientation or identify it with the
  capacity-gated game source.  Those identifications are part of this claim,
  not consequences of block encoding.
- A fresh finite packet at every level gives the same dilution after the
  canonical trace sums the level types.
- Identifying all level heads restores positive density but lets the defect
  amplitude return, so `q u^n q` is no longer `T^n`.
- Exact orthogonality of infinitely many conjugates of `q` cannot be a group
  algebra identity: canonical trace would sum the common positive trace past
  one.  The required no-return law must therefore be a finite-matrix-only
  consequence of a self-similar or multiplicity-rigid relation, not a literal
  orthogonal-shift presentation.
