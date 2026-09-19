---
rg: 2
id: reynolds-exit-does-not-carry-pauli-gauge
kind: claim
title: The Reynolds exit carries assignment mass but not the controlled-Pauli gauge
invalidates:
  - zpc-reynolds-exit-authenticates-identity-copy
distinct_from:
  index-two-reynolds-hnn-is-a-proper-corner-section: that constructs the positive unused range; this proves the existing same-range dressings recover their relative unitary only on the complementary source and used range.
  same-range-dressed-reynolds-sections-expose-raw-source-unitary: that positively recovers a supplied payload on the source; this identifies why that recovery does not reach the Reynolds exit atom needed by the ZPC gauge lock.
  pauli-gauge-word-retains-and-cocycle: that treats arbitrary fixed packet dressing by crossing parity; this gives the exact native dressing identity and locates it relative to the proper section.
---

**ESTABLISHED PROPER-CORNER FIREWALL.**  In the index-two Reynolds HNN
section, write

```text
p=e_C,                 q=e_H,                 v=qup=up,
E_exit=q-vv^*.                                             (REG1)
```

The used range is `vv^*=upu^*`; the exit is orthogonal to it and has the
same tracial mass as the assignment Reynolds surplus `e_H-e_C`.  It need
not equal that source-side projection as an operator.  Every currently
available same-range dressing has the form

```text
v_0=up,                 v_1=udp,                 dp=pd, (REG2)
```

so both paths have source `p`, range `upu^*`, and relative corner

```text
v_0^*v_1=pdp.                                             (REG3)
```

Thus the raw gauge is exposed on `p`, not on any positive subprojection of
`E_exit`.  The existing section supplies assignment mass as an **unused
range**, but supplies no identity-label occurrence on that mass.  Reversing
the edge is not part of the regular-safe construction: the source required
there is a subgroup Reynolds projection, whereas the surplus is a Reynolds
difference/character atom.

Native controlled-Pauli dressing does not move the gauge to the exit.  From
the ordinary relations `(CPM5)` one has the exact word identity

```text
[XU,ZV]=J S T [U,V].                                     (REG4)
```

Indeed expand `XUZVXUZV`, then use `UZ=SZU`, `VX=TXV`,
`XZX=JZ`, and `UVZ=SZUV`.  Equivalently, on selector sector `(a,b)`, the
two sides are

```text
J^((a+1)(b+1))[A,B]
 =J^(1+a+b) J^(ab)[A,B].                                (REG5)
```

After imposing `[U,V]=1`, the dressed commutator is the affine selector word
`JST`; it contains no pure multiplicity information.  On the marked active
atom `J=S=T=-1` it is still `-1`, rather than a commuting identity-label
copy.

Consequently the existing Reynolds section, its same-range payload
dressings, and the native Pauli dressings do not instantiate `(AIM1)` on the
active-mismatch mass.  The smallest surviving proper-corner construction is
a second non-rank-preserving section whose **source** is a positive
subprojection of `E_exit`, or a pair of contractions from that exit with a
positive mixed Gram and an additional row forcing the polar relative gauge
to commute.  This firewall does not refute such a new occurrence.
