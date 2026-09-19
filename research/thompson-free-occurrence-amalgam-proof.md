---
rg: 2
id: thompson-free-occurrence-amalgam-proof
kind: route
title: Present one base occurrence and let its finitely generated stabilizer fix it
target: thompson-free-occurrence-amalgam-preserves-contextuality
requires: []
---

Let `P` be the group defined by the finite presentation `(TFO2)`.  For
`x=gx_0`, define `H_x=gHg^(-1)`.  If `g'x_0=x` as well, then `g'^(-1)g` lies
in the point stabilizer.  Relations `(TFO2)` make that stabilizer centralize
every generator of `H`, so `H_x` is independent of the transporter.

The presentation imposes the relators `R_H` on every conjugate copy and makes
`V` permute the copies.  It imposes no relation involving generators from two
different copies except equality of their central `J`, because every relator
outside `R_H,R_V` lies inside the base stabilizer action or centralizes `J`.
The universal properties of the amalgamated free product and semidirect
product therefore give inverse maps between `P` and `(TFO1)`.

The point stabilizer is finitely generated for the rational-tail action of
`V`, so `(TFO2)` is finite.  Finally the folding map is compatible with the
free amalgam, while killing `V` makes the permutation action trivial.  It is
a retraction onto `H`, proving survival of `J` and every other word surviving
under the fold.
