---
rg: 2
id: cyclic-frequency-ledger-pays-excess-source-rank
kind: claim
title: Cyclic frequency energy pays every source direction beyond the one-mode capacity
distinct_from:
  bs14-source-mode-reset-has-exact-frequency-cost: that gives the exact reset cost of a selected eigenmode and the capacity one statement; this quantitatively charges the excess rank of an arbitrary source subspace before a mode has been selected.
  bs14-regular-character-forces-sublinear-fixed-source: that gives the asymptotic Haar quantile for a global regular-character sequence; this is an exact finite length-m packet inequality with an explicit excess-over-one bound.
  two-source-gram-alignment-pays-frequency-not-mode-purity: that produces one common source and exhibits a rank-one low-frequency mode-purity counterpacket; this shows why that counterpacket is passive and charges every positive excess source rank cubically.
---

**ESTABLISHED.** Let `R` be the return-one cyclic implementer on a
multiplicity-one length-`m` scalar BS packet.  Its Fourier eigenvalues are

```text
lambda_j=exp(2 pi i j/m),             0<=j<m.            (CFR1)
```

Let `W:E -> C^m` be any isometry, put `k=dim(E)`, `q=k-1`, and define its
direct frequency energy

```text
F=||(R-1)W||_F^2.                                       (CFR2)
```

Then

```text
F >= (4/3) q^3/m^2,

q/m <= ((3/4)(F/m))^(1/3).                              (CFR3)
```

### Proof

Put `A=|R-1|^2`.  Its eigenvalues are

```text
a_j=4 sin^2(pi d_j/m),       d_j=min(j,m-j).
```

For `0<=d_j<=m/2`, `sin(pi d_j/m)>=2d_j/m`, hence

```text
a_j>=16 d_j^2/m^2.                                      (CFR4)
```

Since `WW^*` is a rank-`k` projection, Ky Fan's minimum principle gives
`F=Tr(WW^*A)` at least the sum of the `k` smallest eigenvalues of `A`.
After the unique zero mode, the ordered cyclic distances are

```text
1,1,2,2,3,3,...
```

with the evident single terminal entry when `m` is even.  If
`d_(1),...,d_(q)` are the first `q` positive distances, then

```text
sum_(l=1)^q d_(l)^2
 =sum_(l=1)^q ceil(l/2)^2
 >=(1/4)sum_(l=1)^q l^2
 >=q^3/12.                                             (CFR5)
```

Combining `(CFR4)--(CFR5)` proves `(CFR3)`.

## Active/passive consequence

One simple packet has exact neutral-source capacity one by
`bs14-source-mode-reset-has-exact-frequency-cost`.  Discarding the other
`q` source directions costs squared normalized Hilbert--Schmidt mass
`q/m`.  Equation `(CFR3)` therefore gives discard norm

```text
sqrt(q/m) <= ((3/4)(F/m))^(1/6).                         (CFR6)
```

The one retained direction need not itself be a flat cyclic eigenmode.  The
adjacent-mode example below shows that frequency energy cannot pay its
mode-purity correction.  One may always discard that final direction too,
at the separate packet-normalized cost `m^(-1/2)`.  Hence a completely
source-free passive repair has the uniform estimate

```text
sqrt(k/m)
 <= ((3/4)(F/m))^(1/6)+m^(-1/2).                        (CFR7)
```

The extra one-direction tax vanishes on long packets; bounded lengths must
be handled by their finite-level stability or by an authenticated exact
mode reset.

This explains the low-frequency counterpacket in
`two-source-gram-alignment-pays-frequency-not-mode-purity`: one mixed source
can stay far from every flat reset vector at frequency cost `O(m^(-2))`, but
it has `q=0` and occupies only the single unpaid direction in `(CFR7)`.  As
soon as a packet asks for multiple independent sources, the excess rank has
a cubic frequency price.

Combining with `(TSG4)`, two already extracted cubic source isometries may be
Gram-aligned to `W`, after which their inversion defects pay every
beyond-capacity direction at the dimension-free passive rate `(CFR6)`.

## Remaining scope

The theorem applies after a common source has been localized inside one
authenticated simple packet.  It neither makes the last retained vector a
valid flat source nor decomposes an arbitrary polar source across moving BS
packet types, rounds fractional packet weights, or constructs the two exact
cubic exits.  Those are precisely the remaining mode-selection,
carrier-authentication, and integer-duplication parts of
`bs14-residual-polar-data-build-active-dilation`.
