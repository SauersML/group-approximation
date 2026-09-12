---
rg: 2
id: pointwise-a5-overlap-globalizes-carmichael-family
kind: claim
title: Pointwise adjacent A5 overlap synchronizes a full Carmichael family
distinct_from:
  thompson-v-r5-coherent-carmichael-family: that asks the fixed Thompson presentation to produce the required contextual matrices; this is the dimension-free abstract globalization after pointwise overlap control has been supplied.
  thompson-v-r5-coherent-alternating-packet: that asks for an approximate multiplication table on an entire symmetric group; this retains only the Carmichael generators and their pair relators.
  a5-carmichael-triangle-covers-involution-kernels: that is a spectral inequality internal to one exact A5 chart; this synchronizes the contextual copies of each generator across all charts.
---

Let `B in U(d)`, let `M>=3`, and for every three-subset `T` of `[M]` and
every `i in T` let

```text
Y_i^T = W_i^T B (W_i^T)^*
```

be a unitary conjugate of `B`.  Suppose that for some `eta,epsilon>=0`:

```text
||(Y_i^T)^3-I||_2 <= eta,
||(Y_i^T Y_j^T)^2-I||_2 <= eta                 (i!=j in T),       (POG1)
```

and whenever `|T intersect T'|=2`,

```text
||Y_i^T-Y_i^(T')||_2 <= epsilon                (i in T intersect T'). (POG2)
```

Then there are literal unitary conjugates `X_i` of `B`, `1<=i<=M`, such that

```text
||X_i^3-I||_2 <= eta,
||(X_iX_j)^2-I||_2 <= eta+8 epsilon             (i!=j).           (POG3)
```

The constants are independent of `M` and `d`.  In particular pointwise
`O(delta)` synchronization of adjacent Carmichael `A5` charts gives the full
uniform Carmichael family with `O(delta)` defect.  An averaged Poincare
estimate is not substituted for `(POG2)`: the conclusion controls every
pair, including when `M` is chosen after the matrix dimension.

