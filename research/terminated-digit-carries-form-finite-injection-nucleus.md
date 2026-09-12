---
rg: 2
id: terminated-digit-carries-form-finite-injection-nucleus
kind: claim
title: Terminated bijective-base digits have a four-map nucleus of injections
artifacts:
  - research/artifacts/boone-higman-terminated-digit-resolution-2026-09-08.md
---

Fix h>=2 and r>=2. Let Gamma have nodes X,Y, with r edges
0,...,r-1 from X to Y, h loops 1,...,h at Y, and an edge #
from Y to X. Write C_X,C_Y for the two path cones.

There are rational open injections I,D:C_Y->C_Y given by

    I(#z)=1#z,       I(dz)=(d+1)z for 1<=d<h,
    I(hz)=1I(z),

    D(#z)=#z,        D(1z)=hD(z),
    D(dz)=h(d-1)z for 2<=d<=h.

The set N={id_(C_X),id_(C_Y),I,D} is a finite nucleus of
injections in the sense of Belk--Bleak--Matucci--Zaremsky.
Consequently the group H_(h,r) of all rational homeomorphisms of
C_X whose recurrent local actions lie in N is a full contracting
rational similarity group. It is finitely presented and embeds
in a finitely presented simple group.
