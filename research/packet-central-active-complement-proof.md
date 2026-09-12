---
rg: 2
id: packet-central-active-complement-proof
kind: route
title: Expand the commutator of the three endpoint spectral cuts
target: packet-central-active-complement-reduces-shared-words
requires: []
---

Because `J,K,b` commute, the three spectral cuts in `(PAC1)` commute, so
`X=QFB` is a projection below `Q` and `A=Q-X` is a projection.  For any
involution `s`,

```text
||[Y,(I-s)/2]||_2=(1/2)||[Y,s]||_2.                    (1)
```

The product rule gives

```text
[Y,QFB]=[Y,Q]FB+Q[Y,F]B+QF[Y,B].                       (2)
```

Every spectral projection in `(2)` is a contraction.  Hence `(1)--(2)` and
`[Y,A]=[Y,Q]-[Y,X]` imply

```text
||[Y,A]||_2
 <= (1/2)||[Y,J]||_2
   +(1/2)(||[Y,J]||_2+||[Y,K]||_2+||[Y,b]||_2),
```

which is `(PAC2)`.  Moreover

```text
(I-A)[Y,A]A=(I-A)YA,                                   (3)
```

so compression of `(3)` proves `(PAC3)`.

For a word `W=Y_1...Y_L`, expand `[W,A]` by the product rule.  Unitary
invariance and `(PAC2)` bound it by the sum of the endpoint-commutator norms
for the `L` letters.  Cauchy--Schwarz converts this finite sum to `(PAC4)`.
All constants depend only on the fixed word menu, never on matrix dimension.
