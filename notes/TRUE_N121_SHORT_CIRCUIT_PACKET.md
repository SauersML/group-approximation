# An exact short rank-two cellular packet at projective level 121

Date: 2026-08-12

## Outcome

The fundamental-circuit screen at projective level `121` isolates two
exceptionally short homology-bearing cellular cycles.  They lift exactly to
primitive integral vectors `c_1,c_2 in Z^1940` with

```text
|supp(c_1)|=16,   ||c_1||^2=40,   ||c_1||_1=24,
|supp(c_2)|=17,   ||c_2||^2=35,   ||c_2||_1=23,       (NCP1)
```

and every coefficient belongs to `{+-1,+-2}`.  Their exact Gram matrix is

```text
        [40 20]
G_c  =  [20 35].                                    (NCP2)
```

Both are cycles in the integral projective cellular complex.  Their images
in degree-two homology are linearly independent over `Q`.  Thus level `121`
contains an exact rank-two primal homology packet of uniformly local
combinatorial shape, despite the severe density of the default full cycle
basis.

The independent rank two matches the separately proved dimension of the
cuspidal quotient at level `121`; however, the current certificate does not
compute the absolute-to-relative map, so this note does **not** identify the
packet as the cuspidal plane.  The other five homology directions require
large supports in this particular modular pivot basis.  That is evidence
for their boundary-kernel character, not a lower bound against other pivot
choices or other short packets.

Exact data:

```text
experiments/projective-cellular-n121-fundamental-circuit-screen.json
```

Replications of the support and quotient-rank pattern in characteristics
`101` and `10007` are stored in the corresponding suffixed JSON files.

## 1. Cellular complex

For the level-`121` projective cellular complex, the rational chain-group
dimensions are

```text
721 <- 2028 <- 1940 <- 654.                         (NCP3)
```

Write

```text
A=d_2^T:Q^1940->Q^2028,
B=d_3:Q^654->Q^1940.                                (NCP4)
```

The exact ranks are

```text
rank_Q(A)=1308,
rank_Q(B)=625,                                      (NCP5)
```

and `AB^T=0`.  Hence

```text
dim_Q H_2=1940-1308-625=7.                          (NCP6)
```

The matrix `A` has `632`-dimensional cycle kernel.  A right-kernel echelon
basis over `F_1009` is mostly global: median support `1156`, with maximum
support `1256`.  This is not a contradiction to the previously computed
short harmonic packets.  Echelon fundamental circuits depend strongly on
the pivot choice, and harmonic projection can drastically shorten a global
cycle representative.

The useful feature is that two homology-bearing echelon circuits have
supports only `16` and `17`.  The same two row indices and supports occur in
characteristics `101`, `1009`, and `10007`.

## 2. Exact integral lifts

Restrict the integer matrix `A` to each of the two small support sets.  In
both cases the rational kernel has dimension one.  Its primitive integral
generator gives the following cycles.

The first is

```text
c_1 =
  2e_315 -2e_646 +2e_650 -2e_653 +2e_1161
 - e_1851 +2e_1852 + e_1853
 + e_1925 -2e_1926 -2e_1928 - e_1929 - e_1930
 + e_1932 + e_1938 - e_1939.                       (NCP7)
```

The second is

```text
c_2 =
  2e_617 -2e_646 +2e_652 -2e_653
 + e_1901 - e_1902 + e_1903
 + e_1925 -2e_1926 - e_1928 - e_1929 -2e_1930
 + e_1932 + e_1933 - e_1934 + e_1935 - e_1939.     (NCP8)
```

Direct integer multiplication gives

```text
A c_1=A c_2=0.                                     (NCP9)
```

The coefficient gcd is one in both cases, proving primitivity.  Equations
`(NCP1)` and `(NCP2)` follow immediately from `(NCP7)--(NCP8)`; in
particular `<c_1,c_2>=20`.

## 3. Exact rational nontriviality and independence

Over each of `F_101`, `F_1009`, and `F_10007`, the ranks of `A` and `B` are
`1308` and `625`, respectively.  Express the row space of `B` in a basis of
`ker(A)`.  Its annihilator has dimension seven.  The signatures of `c_1`
and `c_2` in this annihilator are independent; equivalently,

```text
rank_Fp [B;c_1;c_2]=627                              (NCP10)
```

for each of the three characteristics.

This proves rational independence without an additional large exact rank
calculation.  Indeed, the rank of an integer matrix modulo a prime is at
most its rational rank, so `(NCP10)` gives

```text
rank_Q [B;c_1;c_2]>=627.                             (NCP11)
```

Since `rank_Q(B)=625`, the two classes are independent in

```text
ker(A)/row_Q(B)=H_2.                                (NCP12)
```

The use of three characteristics is replication; one characteristic with
the certified rank increase already proves `(NCP11)`.

## 4. Consequence for the packet program

Let `P_H` be harmonic projection.  The Hodge isomorphism identifies
homology with the harmonic space, so `(NCP12)` implies

```text
P_H c_1, P_H c_2
```

are independent.  Since projection is contractive,

```text
||P_H c_1||<=sqrt(40),
||P_H c_2||<=sqrt(35).                              (NCP13)
```

Thus two of seven level-`121` directions now have explicit short integral
cycle representatives, not merely a reduced harmonic Gram certificate.
This supplies concrete templates from which a family theorem might be
recognized.

It does not solve the level family.  First, `(NCP13)` is a fixed-chart bound,
not a construction for all square levels.  Second, the remaining five
directions are not handled.  Third, a bounded integral section for circle
repair is stronger than bounded primal representatives.

The structural next step is exact and small: apply the absolute-to-relative
comparison to `c_1,c_2`.  Rank two in the relative image would identify this
packet with the cuspidal quotient and leave the five boundary-kernel
directions as a separate Eisenstein packet problem.

## 5. Reproduction and scope

The screen is implemented by

```text
experiments/sl3_projective_fundamental_circuit_screen.py
```

It performs modular sparse elimination to choose fundamental circuits and
then recomputes every selected circuit of support at most `64` over `Z`.
The exact cycles `(NCP7)--(NCP8)` therefore do not depend on interpreting
balanced finite-field coefficients as integers.

The dense-support values for the other five greedy quotient directions are
only properties of one echelon pivot choice.  They are not claimed as
minimal support, minimal norm, or evidence against the already certified
short harmonic projections at level `121`.
