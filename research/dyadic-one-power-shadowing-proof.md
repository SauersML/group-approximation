---
rg: 2
id: dyadic-one-power-shadowing-proof
kind: route
title: Discard slow short mass and binary-cut every remaining fourth-power packet
target: regular-bs14-cores-admit-dyadic-one-power-shadows
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
  - bs14-long-cycles-admit-bounded-period-shadowing
  - one-unipotent-quotients-are-bounded-congruence
---

Fix `K=2^q`.  By
`bs14-unitary-representations-are-periodic-cycle-packets`, decompose the
exact core into fourth-power packets.  Let `P_(n,K)` be the sum of the
packets of length at most `L_K=Kq`.  This projection reduces both `R_n`
and `S_n`.

## The short carrier has vanishing regular mass

The empirical spectral measures `nu_n` of `S_n` converge weakly to Haar
measure on the circle: their nonzero Fourier coefficients are exactly the
quantities in `(DYS2)`.  For fixed `K`, every eigenvalue belonging to a
packet of length at most `L_K` lies in the finite set

```text
F_K=union_(1<=m<=L_K) {z in T : z^(4^m-1)=1}.        (DYP1)
```

Haar measure gives `F_K` mass zero.  Portmanteau for the closed finite set
therefore gives

```text
mu_n(K)=rank(P_(n,K))/d_n <= nu_n(F_K) ->0.           (DYP2)
```

Replace both generators by the identity on `P_(n,K)`.  This remains an
exact `BS(1,4)` representation and contributes at most `4mu_n(K)` to each
squared normalized Hilbert--Schmidt distance.

## Binary cutting of a long packet

Consider an original packet of length `m>L_K`.  Write

```text
m=aK+r,                 0<=r<K.                       (DYP3)
```

Cut it into `a` consecutive pieces of length `K`, followed by the pieces
given by the binary expansion of `r`.  Every piece length `ell` is a power
of two dividing `K`.  The number `b` of pieces satisfies

```text
b=a+popcount(r) <= m/K+q < 2m/K,                     (DYP4)
```

where the last inequality uses `m>Kq`.

On a piece of length `ell` beginning at spectral angle `alpha`, use the
same nearest-periodic-point construction as in
`bs14-long-cycles-admit-bounded-period-shadowing`: choose

```text
eta=c/(4^ell-1)
```

with `c` nearest to `(4^ell-1)alpha`.  In the fourth-power ordering of the
packet, put the new spectral angles at

```text
eta,4eta,...,4^(ell-1)eta.
```

Close the corresponding shift edge in the orientation dictated by
`R S R^(-1)=S^4`.  Direct substitution then gives the exact relation on
the new piece.  This orientation is only the reversal convention already
present in the periodic-packet normal form; it does not change the metric
estimate.

The squared spectral chordal error summed over one piece is at most
`pi^2/9`, and only one shift edge per piece is changed.  Thus, after
normalizing by the `m` vertices of the original packet, the two squared
costs are at most

```text
4b/m < 8/K,
(pi^2/9)b/m < 2pi^2/(9K).                            (DYP5)
```

The same estimates hold with arbitrary equal packet multiplicity: both
the numerator and the packet dimension acquire that multiplicity.  Summing
orthogonally over all long packets and adding the discarded short carrier
proves `(DYS6)`.

Every new nontrivial packet has length `ell` dividing `K`, so its base
eigenvalues satisfy `z^(4^ell-1)=1`.  The elementary divisibility

```text
ell | K  =>  4^ell-1 | 4^K-1                       (DYP6)
```

and the identity short carrier prove `(DYS7)`.

## The slow diagonal and the quotient scale

For every `q`, `(DYP2)` lets us choose an index `n_q` so large that

```text
n>=n_q  =>  mu_n(2^q)<=2^(-q).
```

Choose the `n_q` increasing and let `q(n)` be the largest `q` with
`n>=n_q`.  Then `K_n=2^q(n)->infinity` and
`mu_n(K_n)<=1/K_n`; `(DYS6)` becomes `(DYS4)`.

Finally put `N=4^K-1`.  By
`one-unipotent-quotients-are-bounded-congruence`, the finite Iwahori quotient
`Q_N` has order comparable, up to constants independent of `N`, to `N^3`.
Therefore

```text
log |Q_N|=3K log 4+O(1)=Theta(K),                    (DYP7)
```

and `(DYS8)` follows.

The diagonal can be chosen arbitrarily slowly, but it cannot make the fixed
preconditioning error for a chosen `K` smaller than order `K^(-1/2)`.
Consequently this proof sharpens the quotient-size exponent and does not by
itself cross the moving fixed-level basin.
