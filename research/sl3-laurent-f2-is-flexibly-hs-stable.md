---
rg: 2
id: sl3-laurent-f2-is-flexibly-hs-stable
kind: claim
title: SL_3(F_2[t,1/t]) is flexibly Hilbert--Schmidt stable
distinct_from:
  el-r-polynomial-vertex-not-flexibly-hs-stable: that concerns instability of the polynomial vertex SL_3(F_q[t]) and EL_3(F_q[x]), using that they are infinitely presented; this is stability of the Laurent host SL_3(F_2[t,1/t]) that contains the vertex as a co-dense subgroup
  stable-group-with-codense-kazhdan-subgroup: that asks for any stable host with a co-dense Kazhdan subgroup; this names one candidate whose Kazhdan and co-density hypotheses are proved
---

**OPEN.**  `A=SL_3(F_2[t,1/t])` is flexibly Hilbert--Schmidt stable, in the
sense consumed by the corollary of
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear` (Dogon--Vigdorovich's
flexible notion).

Consequences, through the routes below:
- `<A,s | [s,SL_3(F_2[t])]=1>` is non-hyperlinear;
- `L(SL_3(F_2[t])) subset L(A)` is not `RE/C`;
- the Kun--Thom double at `(q,r)=(2,3)` is non-hyperlinear for every `d>=3`,
  and so is the opposite-slice double.

## Attempts

- **Strict stability is excluded.**  `A` is residually finite and Kazhdan
  (`elementary-groups-over-fg-rings-have-property-t`).  By the graph's node
  `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`, same-dimension
  stability fails.  Only the flexible form is open.
- **Vertex instability does not transfer.**  The route
  `el-r-vertex-instability-via-rank-three-covers` looks for non-roundable
  models of the infinitely presented vertex `SL_3(F_q[t])`.  Such models are
  not models of `A`, and restricting a model of `A` to the vertex does not
  produce them.
- **Number-field analogue.**  The same statement for `SL_3(Z[1/2])` feeds
  `non-hyperlinear-from-hnn-over-sln-z` and is open.  No tool specific to
  characteristic `p` is known to help.  The torus recurrence proving
  co-density is exact and says nothing about approximate models.
