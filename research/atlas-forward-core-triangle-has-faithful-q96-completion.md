---
rg: 2
id: atlas-forward-core-triangle-has-faithful-q96-completion
kind: claim
title: The collision and core A4 edges have a faithful order-96 triangle completion
artifacts:
  - experiments/atlas_a4_q96_triangle_completion.g
  - research/artifacts/atlas-a4-q96-triangle-completion.json
distinct_from:
  atlas-a10-first-core-cycle-collapses: that proves the corresponding triangle over the marked A10 carrier collapses; this changes the carrier and gives a finite universal completion with every local edge embedded.
  atlas-s576-carrier-completes-first-core-k22: that completes the entire first core rectangle by a regular amalgam; this isolates the smaller collision/core triangle before the central 144-state vertex is closed back around it.
---

Let `c,u` be commuting involutions and let `t` have order three.  The two
adjacent regular-`A4` contexts impose

```text
(ct)^3=(ut)^3=1.
```

Their universal triangle completion is

```text
Q96=<c,u,t | c^2,u^2,t^3,[c,u],(ct)^3,(ut)^3>,
|Q96|=96.                                                   (Q96-1)
```

All three finite edge groups inject:

```text
<c,u> ~= C2 x C2,       |<c,u>|=4,
<c,t> ~= A4,            |<c,t>|=12,
<u,t> ~= A4,            |<u,t>|=12.                       (Q96-2)
```

GAP identifies the order-96 structure as

```text
((C2 x C2 x C2) : (C2 x C2)) : C3.
```

Thus the spherical Gersten--Stallings angle sum at this three-edge seam does
not signal collapse: the universal completion is already finite and faithful
on every edge.  Any obstruction must close at least one further cycle, such
as the simultaneous attachment of the `C2^4:C3^2` forward vertex along its
marked `C3^2` and `C2` subgroups.
