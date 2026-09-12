---
rg: 2
id: iwahori-cycle-packet-determinant-fence
kind: claim
title: The two Iwahori cubics impose an exact determinant congruence on every scalar BS(1,4) cycle packet
distinct_from:
  iwahori-weil-cycle-packets-extend-exactly: that constructs packets passing all relations; this is a necessary scalar condition which eliminates many packets but is not sufficient.
  additive-index-instability: that records why determinant and additive-index data cannot yield an amplification-stable microstate obstruction; this uses determinant only as an exact fixed-packet classifier and explicitly claims no robust global gap.
  bs14-unitary-representations-are-periodic-cycle-packets: that supplies the scalar packet normal form; this applies the two additional cubic relations to its determinant data.
---

Let `(R,S)` be a multiplicity-one fourth-power cycle packet of length `m`,
with

```text
S=diag(lambda,lambda^4,...,lambda^(4^(m-1))),
R^m=v I,          v in T.                              (PDF1)
```

If an involution `X` extends this packet through the two exact cubics

```text
(X S^2)^3=1,
(X R S)^3=1,                                         (PDF2)
```

then necessarily

```text
[(det R)/(det S)]^3=1.                               (PDF3)
```

In the packet coordinates,

```text
det R=(-1)^(m-1) v,
det S=lambda^((4^m-1)/3),                            (PDF4)
```

so the explicit fence is

```text
[(-1)^(m-1) v lambda^(-(4^m-1)/3)]^3=1.              (PDF5)
```

For a primitive `p`-th root with prime `p!=3` and
`m=ord_p(4)`, the geometric sum in `(PDF4)` is divisible by `p`, hence
`det S=1`.  A packet with `v=+1` can therefore extend only when `m` is odd.
In particular, if `m=(p-1)/2`, every prime `p=1 mod 4` is excluded, while
the Weil family `p=3 mod 4` passes this necessary test.  This exactly
accounts for the large probe residuals at `p=5,13,17` before any nonlinear
phase optimization is considered.

The condition is not sufficient: the tested packets at `q=31,43` pass the
determinant fence but retain large cubic residuals.  Nor is `(PDF5)` a
normalized-HS soundness gap.  A determinant discrepancy can be hidden in
`o(d)` spectral directions after amplification, as recorded by
`additive-index-instability`.  The result is useful only
for exact packet classification and for pruning the transport problem before
one seeks a positive-density invariant.
