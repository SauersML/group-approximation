---
rg: 2
id: cyclic-frequency-excess-source-rank-proof
kind: route
title: Apply Ky Fan after counting the repeated cyclic distances
target: cyclic-frequency-ledger-pays-excess-source-rank
requires: []
---

Write `P=WW^*`, a rank-`k` orthogonal projection, and

```text
A=(R-1)^*(R-1)=|R-1|^2.
```

Because the Frobenius norm here is unnormalized,

```text
F=Tr(W^*AW)=Tr(PA).                                     (CFR8)
```

The eigenvalue belonging to cyclic frequency `j` is

```text
a_j=|exp(2 pi i j/m)-1|^2
   =4 sin^2(pi d_j/m),        d_j=min(j,m-j),            (CFR9)
```

and occurs `n` times.  For `0<=d_j<=m/2`, concavity of sine on
`[0,pi/2]` gives `sin(pi d_j/m)>=2d_j/m`, and hence

```text
a_j>=16d_j^2/m^2.                                      (CFR10)
```

Ky Fan's minimum principle says that `Tr(PA)` is at least the sum of the
`k` smallest eigenvalues of `A`.  There are exactly `n` zero eigenvalues.
Let `delta_1<=...<=delta_(n(m-1))` be the positive cyclic distances with
multiplicity.  Every distance strictly below `m/2` occurs `2n` times; when
`m` is even the terminal distance `m/2` occurs only `n` times.  In either
case

```text
delta_l>=l/(2n).                                        (CFR11)
```

Indeed the last index at a nonterminal distance `d` is `2nd`, while the
last index at the even terminal distance is `n(m-1)<=2n(m/2)`.  If
`q=max(k-n,0)`, Ky Fan, `(CFR10)`, and `(CFR11)` yield

```text
F >=(16/m^2) sum_(l=1)^q delta_l^2
  >=(4/(n^2m^2)) sum_(l=1)^q l^2
  >=(4/3)q^3/(n^2m^2),                                  (CFR12)
```

where the final inequality follows from
`sum_(l=1)^q l^2>=integral_0^q t^2 dt=q^3/3`.  This also covers `q=0`;
when `m=1`, the isometry forces `k<=n`, so again `q=0` and the assertion is
immediate.  Thus there is no omitted odd/even or zero-rank case.

Dividing `(CFR12)` by `mn` gives

```text
F/(mn)>=(4/3)(q/(mn))^3,
```

which is exactly the second inequality in `(CFR3)` after taking cube
roots.

For the deletion statements, discard any `q` orthogonal source directions
and retain `min(k,n)` directions.  Since `W` is isometric, the discarded
map has Frobenius norm squared `q`, hence normalized squared mass `q/(mn)`;
taking square roots in `(CFR3)` proves `(CFR6)`.  Moreover

```text
k/(mn)<=q/(mn)+1/m.
```

Using `sqrt(a+b)<=sqrt(a)+sqrt(b)` proves `(CFR7)`.  The return-one cyclic
operator has fixed eigenspace of dimension `n` (one fixed mode in each of
the `n` scalar copies), so there can be at most `n` independent fixed
neutral sources.  Nothing in the rank deletion makes the retained sector
mode-pure, in agreement with the stated firewall.  Finally, whenever a
separately constructed common source satisfies `(TSG4)`, substituting that
upper bound for `F` in `(CFR6)` gives the claimed conditional two-source
consequence; no mode-selection conclusion is used or obtained.
