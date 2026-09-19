---
rg: 2
id: kt-literal-return-stays-far-from-edge-normalizers
kind: claim
title: The literal Kun--Thom return remains far from every edge-normalizer gauge
distinct_from:
  kt-return-compressor-gauges-separate: That gives two separate exact finite gauges with the same abstract correspondence data; this uses the literal mixed word to prove that the returned gauge itself stays a fixed normalized-HS distance from every edge normalizer.
  marked-double-coset-infinite-degree: That computes the exact infinite degree of the marked double coset; this converts one fixed exterior neighbour into a quantitative conditional-expectation separation inequality in matrix microstates.
  exterior-return-generates-almost-full-right-edge-module: That authenticates almost full right-module dimension after subtracting the edge expectation; this shows that the same corrected cyclic vector cannot implement the compressor normalizer action.
---

Let `Gamma<G` be the Laurent Kun--Thom pair, let `h in G` be the marked
element, and put `B=C*(phi(Gamma))` in a finite-dimensional relative
microstate.  For the literal return

```text
x=T^* phi(gamma) T,
```

assume `x` is unitary (rounding an asymptotic unitary changes all estimates
by the rounding error).  Choose one fixed `delta in Gamma` such that

```text
k=h^(-1) delta h notin Gamma,                           (LRN1)
```

which exists because the marked double coset has infinite degree, and set
`a=phi(delta) in B`.  Write

```text
omega=||x^* a x-phi(k)||_2,
q_k=||E_B(phi(k))||_2.
```

Then

```text
dist_2(x,N(B)) >= (1-q_k-omega)/2,                     (LRN2)
```

where `N(B)={w in U(d):w^*Bw=B}`.  In canonical relative microstates
`q_k->0`, while fixed-word multiplicativity gives `omega->0`; consequently

```text
liminf dist_2(x,N(B)) >= 1/2.                          (LRN3)
```

The separation survives the correction used to extract the almost-full
right edge module.  Put `z=E_B(x)`, `y=x-z`, and let `v` be a unitary polar
extension closest to `y`.  If `s=||z||_2`, then

```text
||v-x||_2 <= 2s,
dist_2(v,N(B)) >= 1/2-(q_k+omega)/2-2s.                (LRN4)
```

Thus whenever the returned-edge expectation and the exterior mixed moment
vanish, both the literal word and its unitary correction remain uniformly
far from every compressor/normalizer gauge.  The right module `yB` can have
dimension tending to one, but its left saturation is the infinite-degree
marked-double-coset correspondence rather than an index-one compressor
correspondence.  Any successful Certificate C argument must introduce a
second coupled gauge or a genuinely new holonomy comparison; it cannot
identify the returned-root cyclic vector itself with the compressor gauge.

DERIVATION
kt-literal-return-normalizer-separation-proof
