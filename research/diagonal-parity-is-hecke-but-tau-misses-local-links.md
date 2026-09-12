---
rg: 2
id: diagonal-parity-is-hecke-but-tau-misses-local-links
kind: claim
title: The diagonal parity curl is a two-idempotent Hecke operator, but property tau misses its local links
distinct_from:
  proper-torus-diagonal-code-is-incomplete-cover-curl: that constructs the gain-cover cell complex and identifies its cellular curl; this gives the automorphic blocks and an explicit vanishing-link-gap congruence family.
  diagonal-exact-inversion-is-two-cubic-parity-code: that derives the binary syndrome from diagonal involution gauges; this compares the resulting binary operator with its complex Hecke lift.
  proper-torus-reynolds-is-edge-refinement: that proves divergence for a real signed infinity-norm Green operator; this proves a different spectral no-go directly in the links of the binary curl complex.
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that supplies the global congruence gap; this proves that the gap does not pass to the links needed by a local-to-global binary decoder.
---

**ESTABLISHED; EXACT HECKE IDENTIFICATION AND SHARP PROPERTY-TAU
FIREWALL.** Let (m) be odd and put

```text
G_m=SL_2(Z/mZ)/{+-I},   t=u(1),   r=h(2),   x=w,
a=xt,                   b=xt^2r,
A=<a>,                  B=<b>,
H=<r>,                  N=<H,x>,  P=UH.                 (DHT1)
```

Thus (A) and (B) have order three. On functions on (G_m), write
(L_g f(q)=f(g^{-1}q)), and for a finite subgroup (J) write

```text
e_J=|J|^(-1) sum_(j in J) L_j.                          (DHT2)
```

Lift a function on (N\G_m) to an (N)-invariant function on (G_m).
The integral incidence operator whose reduction modulo two is the
diagonal parity curl is

```text
D_m f=(
 (1+L_a+L_a^2)f,
 (1+L_b+L_b^2)f
).                                                       (DHT3)
```

Over the complex numbers this is exactly

```text
D_m=3(e_A,e_B)|_(Ran e_N),
D_m^*D_m=9 e_N(e_A+e_B)e_N.                             (DHT4)
```

It is therefore a two-idempotent Hecke compression. Under the right
regular action, its block on an irreducible (G_m)-module (V_pi) is

```text
9 e_N(e_A+e_B)e_N on V_pi^N,                            (DHT5)
```

with coefficient multiplicity (V_pi^*). This is the exact automorphic
spectral problem. It is not the Cayley averaging operator controlled by
Selberg's property tau.

There is also a sharp cyclic-label warning. For a prime field, the
oriented edge module is (k[H\G_m]), with left label action by
(T_s/H). If (i=[T_s:H]) is odd and (k) is a characteristic-two
splitting field, Maschke gives its character decomposition and (x)
pairs the (chi) and (chi^{-1}) summands. If (i) is even, the
two-primary label algebra is not semisimple and has its augmentation-ideal
filtration instead. In either case the selected face set has degree one,
not (i), over the full-torus face set. Consequently the curl is not a
deck-equivariant lift and a label Fourier decomposition of the edge space
does not by itself block-diagonalize (DHT3). The right-(G_m) blocks
(DHT5), not independent deck characters, are the honest automorphic
blocks.

The missing local expansion can fail maximally while the global
congruence gap remains uniform. At the vertex (P) of the cell complex
(K_H), identify the incident edges (H\P) with (Z/mZ). If
(d=ord_m(4)) and

```text
K_m={4^j:0<=j<d},
```

then the normalized link adjacency is as follows. If `ell=|H|`,
each displayed step occurs with multiplicity `ell/d`; this multiplicity
cancels against the link degree `4ell`:

```text
(L_link f)(z)
 =1/(4d) sum_(q in K_m) [
    f(z+q)+f(z-q)+f(z+q/2)+f(z-q/2)
  ].                                                     (DHT6)
```

Here (q/2) uses the inverse of two modulo (m). For

```text
m_n=4^n-1
```

one has (ord_(m_n)(4)=n). The nonconstant additive character

```text
phi_n(z)=exp(4 pi i z/m_n)
```

is a link eigenfunction with eigenvalue

```text
lambda_n
 =1/(2n) sum_(j=0)^(n-1) [
    cos(4 pi 4^j/m_n)+cos(2 pi 4^j/m_n)
  ],                                                     (DHT7)
```

and

```text
0 <= 1-lambda_n
 <= (pi^2/(3n)) (4^n+1)/(4^n-1)
 < 4/n.                                                  (DHT8)
```

Thus the link spectral gaps tend to zero along an explicit odd
congruence family. This coexists with the uniform global congruence gap
from Selberg/property tau. Therefore property tau, global automorphic
temperedness, or a local-to-global theorem whose hypotheses require a
uniform link gap cannot by itself prove the Hamming modulus for these
proper-label complexes.

This does **not** refute the diagonal Hamming decoder: a complex may have
binary coboundary soundness for reasons not visible in its worst link
eigenvalue. It proves the exact no-go that any positive proof must use
additional mod-two cosystolic or arithmetic information beyond the
available global property-tau spectrum. The diagonal decoder and the
non-hyperlinearity root remain open.

DERIVATION
diagonal-parity-hecke-link-firewall-proof
