---
rg: 2
id: two-jump-cycle-refutes-functional-calculus-gauge-bound
kind: claim
title: Two phase jumps refute a nonlinear HS gauge bound from coboundary size
distinct_from:
  long-cycles-have-unbounded-l2-coboundary-inverse: that uses a delocalized first Fourier mode and is a linear inverse obstruction; this is an exact nonlinear unitary coboundary with residual supported on two cycle sites.
  normalized-hs-taylor-remainder-is-not-dimension-free: that gives a rank-one second-derivative obstruction for word maps; this gives the corresponding global obstruction for the exact unitary coboundary map.
  iwahori-cubics-control-aggregate-weighted-bs-orbit-energy: that may still hold because its right side is the full Iwahori relator energy; this proves that residual HS size plus functional calculus cannot prove it.
  opposite-root-orthogonality-charges-two-jump-gauges: that proves the Weyl involution row detects these same plateaux in exact left regular congruence packets; this isolates what extra full-group information is needed.
---

There is no dimension-free modulus `g(delta)->0` with the following
property: for every finite tracial abelian algebra, every trace-preserving
cyclic-shift automorphism `psi`, and every exact unitary coboundary

```text
e=c psi(c)^(-1),       ||e-1||_2<=delta,
```

one can choose a solution `c_0` with

```text
||c_0-1||_2<=g(delta).                                (TJC1)
```

Indeed, for even `L` take `A_L=C^(Z/LZ)` with normalized trace and let
`psi` be the cyclic shift.  Put

```text
c_L(j)= 1   for 0<=j<L/2,
        -1  for L/2<=j<L.
```

Then `e_L=c_L psi(c_L)^(-1)` equals `-1` at exactly the two boundary
edges and equals `1` elsewhere.  Hence

```text
||e_L-1||_2^2=8/L -> 0.                               (TJC2)
```

All solutions of `e_L=c psi(c)^(-1)` differ from `c_L` by a
`psi`-fixed unitary, hence by one scalar `zeta in T`.  But

```text
||zeta c_L-1||_2^2
 = (1/2)|zeta-1|^2+(1/2)|zeta+1|^2
 = 2.                                                  (TJC3)
```

Thus every correcting gauge has distance exactly `sqrt(2)` from `1`, even
though the exact coboundary residual tends to zero.

This cycle occurs inside the arithmetic BS packets used elsewhere in the
lane.  For even `L`, take `N=4^L-1`; multiplication by four has an orbit of
length exactly `L` on the exponent-one character of `C_N`.  The diagonal
algebra on that orbit is a copy of `A_L`, and `psi=Ad(h)` is its cyclic
shift.  Hence the packet is not an abstract automorphism pathology: it is
present in exact odd congruence skeletons (where the completed global
congruence repair theorem bypasses it using the other group relations).
In fact `opposite-root-orthogonality-charges-two-jump-gauges` computes that
the Weyl involution row has defect exactly `sqrt(2)` on this gauge in the
left regular arithmetic packet.  Thus the example refutes residual-only
functional calculus, not full-group coercivity.

This is the nonlinear rank-concentration form of the normalized-HS Taylor
failure.  Spectral rounding, taking logarithms on the good spectrum, or
polar decomposition cannot produce a global gauge bound: the two bad
spectral sites have vanishing trace, but their phase jumps separate two
positive-trace plateaux.  A valid Iwahori estimate must therefore use the
involution and cubic relators to charge those plateaux (or show they are an
exact removable representation summand); it cannot be derived from the
Weyl coboundary residual and its cycle holonomy alone.
