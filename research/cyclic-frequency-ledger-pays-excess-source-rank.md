---
rg: 2
id: cyclic-frequency-ledger-pays-excess-source-rank
kind: claim
title: Cyclic frequency energy pays every source direction beyond packet multiplicity
distinct_from:
  bs14-source-mode-reset-has-exact-frequency-cost: that gives the exact reset cost of a selected eigenmode and the capacity one statement; this quantitatively charges the excess rank of an arbitrary source subspace before a mode has been selected.
  bs14-regular-character-forces-sublinear-fixed-source: that gives the asymptotic Haar quantile for a global regular-character sequence; this is an exact finite length-m packet inequality with an explicit excess-over-one bound.
  two-source-gram-alignment-pays-frequency-not-mode-purity: that produces one common source and exhibits a rank-one low-frequency mode-purity counterpacket; this shows why that counterpacket is passive and charges every positive excess source rank cubically.
---

**ESTABLISHED.** Let `R` be the return-one cyclic implementer on a length-`m`
scalar BS packet with multiplicity `n`.  Thus `dim(H)=mn`, and its Fourier
eigenvalues are

```text
lambda_j=exp(2 pi i j/m),             0<=j<m,             (CFR1)
```

each repeated `n` times.  Let `W:E -> H` be any isometry, put

```text
k=dim(E),                 q=max(k-n,0),
```

and define its direct frequency energy

```text
F=||(R-1)W||_F^2.                                       (CFR2)
```

Then

```text
F >= (4/3) q^3/(n^2 m^2),

q/(mn) <= ((3/4)(F/(mn)))^(1/3).                         (CFR3)
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
The zero mode has multiplicity `n`.  After it, the ordered cyclic distances
are

```text
1 repeated 2n times, 2 repeated 2n times, ...
```

with the evident single terminal entry when `m` is even.  If
`d_(1),...,d_(q)` are the first `q` positive distances, then

```text
sum_(l=1)^q d_(l)^2
 >=sum_(l=1)^q (l/(2n))^2
 >=q^3/(12n^2).                                        (CFR5)
```

Combining `(CFR4)--(CFR5)` proves `(CFR3)`.

## Active/passive consequence

A multiplicity-`n` packet has exact neutral-source capacity at most `n`:
after diagonalizing its return unitary, each scalar cyclic copy supplies at
most one fixed source by
`bs14-source-mode-reset-has-exact-frequency-cost`.  Discarding the other
`q` source directions costs squared normalized Hilbert--Schmidt mass
`q/(mn)`.  Equation `(CFR3)` therefore gives discard norm

```text
sqrt(q/(mn)) <= ((3/4)(F/(mn)))^(1/6).                   (CFR6)
```

The retained at-most-`n` dimensional source need not itself split into flat
cyclic eigenmodes.  The
adjacent-mode example below shows that frequency energy cannot pay its
mode-purity correction.  One may always discard that final capacity sector
too, at the separate packet-normalized cost `m^(-1/2)`.  Hence a completely
source-free passive repair has the uniform estimate

```text
sqrt(k/(mn))
 <= ((3/4)(F/(mn)))^(1/6)+m^(-1/2).                     (CFR7)
```

The extra one-direction tax vanishes on long packets; bounded lengths must
be handled by their finite-level stability or by an authenticated exact
mode reset.

The case `n=1` explains the low-frequency counterpacket in
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
authenticated scalar packet (with arbitrary multiplicity).  It neither
makes the retained capacity sector a valid sum of flat sources nor
decomposes an arbitrary polar source across moving BS packet types, rounds
fractional packet weights, or constructs the two exact cubic exits.  Those
are precisely the remaining mode-selection,
carrier-authentication, and integer-duplication parts of
`bs14-residual-polar-data-build-active-dilation`.
