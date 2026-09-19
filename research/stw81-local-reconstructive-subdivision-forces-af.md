---
rg: 2
id: stw81-local-reconstructive-subdivision-forces-af
kind: claim
title: Every locally reconstructive outgoing-colour subdivision collapses a projectionless fibre
distinct_from:
  stw81-shared-unit-two-chart-patching-forces-af: that theorem treats two fixed local factorizations and recovers them from two scalar mixtures; the present theorem permits arbitrary finite, base-dependent subdivisions and works at one transition point, provided each chart is reconstructed separately there.
  stw81-projectionless-rotating-overlap-degeneracy: that theorem treats two frames which each return the whole unit; the present theorem normalizes frames returning unequal scalar portions `1-gamma` and `gamma`, then uses the heavy frame to obtain an unscaled one-colour approximation.
  stw82-support-local-coupled-covers-merge-colours: that theorem supplies a sufficient mechanism for subdividing and merging outgoing maps; the present theorem shows that applying such a mechanism separately to the two charts cannot yield a two-colour interval proof over a non-AF projectionless fibre.
artifacts:
  - research/artifacts/stw81-local-reconstructive-subdivision-firewall-2026-08-30.md
---

Let `D` be a unital projectionless C-star algebra, fix
`gamma in (0,1)`, and suppose that for every finite set `E` in the unit
ball and arbitrarily small `epsilon>0`, there are c.p.c. maps

```text
S_i^r:D->D,                 r,i in {0,1},             (LRS1)
```

each factoring through a finite-dimensional algebra with c.p.c. order-zero
return, such that

```text
norm((S_0^0+S_1^0)(a)-(1-gamma)a)<epsilon,
norm((S_0^1+S_1^1)(a)-gamma a)<epsilon               (LRS2)
```

for `a in E union {1_D}`, and corresponding return maps have orthogonal
ranges across the two rows:

```text
range(phi_i^0) range(phi_i^1)=0,       i=0,1.         (LRS3)
```

Then `D=C1_D`.

This criterion applies to outgoing-colour subdivision with no bound on its
finite depth.  Namely, split each local outgoing map into finitely many
c.p.c. order-zero pieces, assign every piece one of two global labels, and
suppose:

1. pieces with one global label have mutually orthogonal ranges after
   localization, so their direct sum is one c.p.c. order-zero map; and
2. summing all pieces belonging to either original chart reconstructs that
   chart's scalar-weighted local approximation with vanishing error.

Duplicate the original incoming coordinate into the finite copies and
regroup by the two labels.  Evaluation at a transition point where the
chart weights are `1-gamma` and `gamma` gives (LRS1)--(LRS3), hence forces
the fibre to be scalar.

Therefore neither bounded subdivision depth nor depth tending to infinity
can evade the projectionless overlap firewall if each chart is
reconstructed separately at even one fixed genuine overlap weight.  For
`C([0,1]) tensor Z`, an outgoing split can survive only if it is **jointly
reconstructive**: the pieces assigned to the two charts must not separately
approximate their scalar shares, and the approximation must emerge only
after base-dependent coupling across charts.  This is no longer a purely
outgoing local subdivision; it is the incoming-coupled mechanism.

DERIVATION
[[stw81-normalize-unequal-frames-and-drop-heavy-colour]]
