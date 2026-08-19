# Full exact integral cycle packets at square levels 49, 121, and 169

Date: 2026-08-12

## 1. Outcome

The sparse fundamental-circuit screen now gives complete, exact rational
homology packets in the projective cellular complexes at levels

```text
49=7^2,       121=11^2,       169=13^2.                 (SCP1)
```

Every displayed packet vector is an integral cellular two-cycle.  Every
vector is primitive, and the packet spans the full rational `H_2`.  The
quantitative data are:

| level | `dim_Q H_2` | packet supports | largest coefficient | largest squared norm |
|---:|---:|:---|---:|---:|
| 49 | 1 | `11` | 2 | 32 |
| 121 | 7 | `78,98,112,121,124,213,311` | 4 | 871 |
| 169 | 12 | `7,112,134,146,174,183,198,199,204,207,207,220` | 7 | 942 |

Thus the five apparently dense directions at level `121`, and the eight
apparently dense directions at level `169`, were not geometric lower
bounds.  They were artifacts of the natural column order in sparse
echelon elimination.  Reversing the degree-two cellular coordinate order
exposes a full exact packet with small integer coefficients.

There is a second striking decomposition.  In the natural coordinate order,
the exact short subpacket ranks at levels `121` and `169` are respectively

```text
2 and 4,                                                (SCP2)
```

which are exactly the cuspidal dimensions computed by Ash--Yasaki.  The
remaining dimensions are respectively `5` and `8`, exactly the square-level
Eisenstein dimensions

```text
(p-1)(p-5)/12.                                        (SCP3)
```

This numerical agreement does **not** identify the natural-order short
subpackets as cuspidal: that still requires the absolute-to-relative
comparison map.  It is nevertheless a precise new target for that map.

The result is substantial evidence for bounded arithmetic packets, but it
is not a uniform theorem.  The packet supports above are finite-level
bounds, not a level-independent bound, and rational spanning does not prove
that the cycles form a primitive integral basis modulo boundaries.

## 2. Exact ranks

Write the signed cellular complex as

```text
C_3 --d_3--> C_2 --d_2--> C_1.                       (SCP4)
```

At level `49`, the exact rational dimensions and ranks were already
certified:

```text
dim C_2=320,       rank d_2=218,       rank d_3=101,
dim H_2=1.                                            (SCP5)
```

At level `121`, they are

```text
dim C_2=1940,      rank d_2=1308,      rank d_3=625,
dim H_2=7.                                            (SCP6)
```

At level `169`, the newly exported complex has dimensions

```text
Q^1359 <- Q^3888 <- Q^3768 <- Q^1266.                (SCP7)
```

Reduction in each of the three independent characteristics
`101,1009,10007` gives

```text
rank d_2=2530,       rank d_3=1226,       dim H_2=12. (SCP8)
```

The square-level boundary theorem gives Eisenstein dimension eight at
`p=13`, while Ash--Yasaki compute cuspidal dimension four at level `169`.
The exact sequence

```text
0 -> (E^2)^* -> H_2 -> H_cusp^3 -> 0                 (SCP9)
```

therefore gives the matching rational lower bound `8+4=12`.  Hence the
modular ranks in `(SCP8)` equal the rational ranks, and

```text
dim_Q H_2(Gamma_0(169,3);Q)=12.                       (SCP10)
```

## 3. Exact packet construction

Let

```text
A=d_2^T:Z^(C_2)->Z^(C_1).                            (SCP11)
```

Over `F_1009`, compute a right-kernel echelon basis of `A`.  Express the
rows of `d_3` in this cycle basis and use the right kernel of their
coordinate matrix to test whether a circuit contributes a new homology
direction.  Greedily select circuits in increasing support order.

For each selected support `S`, return to the exact integer submatrix `A_S`.
In every case recorded here,

```text
rank_Z ker(A_S)=1.                                   (SCP12)
```

Its primitive generator is the exact cycle.  The program verifies

```text
A c=0                                                (SCP13)
```

over the integers and verifies that its reduction is a scalar multiple of
the selected modular circuit.  Finally, the selected quotient signatures
have full rank over `F_1009`.  Since the modular and rational boundary ranks
agree at these levels, the exact cycles span rational homology.

The coordinate order is mathematically consequential only for which
fundamental circuits the echelon algorithm displays.  It does not change
the complex.  Natural, reverse, and one deterministic shuffled order were
tested.  At level `169`:

- natural order exposes four exact circuits of supports `5,18,20,23`, then
  eight rows of support about `2240`;
- reverse order exposes all twelve directions with support at most `220`;
- a generic shuffled order produces dense circuits of support about `1900`.

Thus arbitrary pivoting is not a certificate of sparsity or nonsparsity.
The reverse order is exploiting structure in the cellular coordinate
filtration.

## 4. Exact Gram matrices

The full level-`121` packet has exact Gram matrix

```text
[[ 78,   9,  13, -16,   4, -25,   22],
 [  9,  98,   7,  -8,  -9,   9,  -18],
 [ 13,   7, 115,  -6,  12, -37,   17],
 [-16,  -8,  -6, 164, -19,  24,  -69],
 [  4,  -9,  12, -19, 133, -39,  -20],
 [-25,   9, -37,  24, -39, 278, -102],
 [ 22, -18,  17, -69, -20,-102,  871]].              (SCP14)
```

Its maximum absolute row sum is `1119`.  Since orthogonal harmonic
projection is contractive, this is a crude exact upper bound on the squared
synthesis norm of the projected packet.  It is much weaker than the already
known reduced harmonic Gram certificate; its value is that the vectors are
literal integral cellular cycles.

At level `169`, the full `12 x 12` Gram matrix is stored in the certificate.
Its maximum absolute row sum is `1658`.  The first reverse-order class is
orthogonal to the other eleven and is the seven-term unit-coefficient cycle

```text
||c||^2=7.                                             (SCP15)
```

The natural-order rank-four subpacket has Gram matrix

```text
[[ 5,  0,   0,   0],
 [ 0, 36,  13, -21],
 [ 0, 13,  32, -23],
 [ 0,-21, -23,  50]].                                 (SCP16)
```

The level-`49` generator has squared norm `32`.  The natural level-`121`
rank-two subpacket has Gram matrix

```text
[[40,20],
 [20,35]].                                             (SCP17)
```

## 5. What this changes for TRUE

This closes one misleading branch of the arithmetic diagnosis.  Large
echelon rows at levels `121` and `169` are not evidence for intrinsic
numerator growth.  Every rational homology direction at both levels has a
literal primitive integral representative with single-digit coefficients.

The remaining family problem is sharper:

1. explain the reverse-order packet by a level-independent cellular or
   Eisenstein/modular-symbol construction;
2. bound its support and synthesis norm uniformly, rather than separately
   at each level; and
3. prove integral saturation and a bounded section for the cuspidal--
   Eisenstein extension.

The nonmonotone observed maxima

```text
311 at 11^2,       220 at 13^2                           (SCP18)
```

are encouraging but prove no asymptotic bound.  Conversely, the existence
of full exact packets at two successive nontrivial square levels makes a
claim of unavoidable growing integral support untenable without a genuine
lower bound.

## 6. Certificates

```text
experiments/projective-cellular-n49-fundamental-circuit-screen-current.json
SHA-256 3be1396161906335f84a551a30f4793c160fe2d4ed410f63cbb053e2022bbdde

experiments/projective-cellular-n121-fundamental-circuit-screen-reverse-exact.json
SHA-256 f2bd8b5217d6436c294a292f78099a9763c6bbbd69181452662750554f6885b6

experiments/projective-cellular-n169-modular-screen.json
SHA-256 08abff92b025bd4760c4a6de2127956500af059cf90a9e4f5717d2b411f0979c

experiments/projective-cellular-n169-fundamental-circuit-screen.json
SHA-256 cd71ef3831abbd667f91e6221318385589b7ce2734765d5cccbeb31ad32306a8

experiments/projective-cellular-n169-fundamental-circuit-screen-reverse-exact.json
SHA-256 fac9b9509b324b829e0a4cc598bf65afa282933a6cdfad14ea1eb0f611bae3a4
```

The point-orbit decoder reproduces the exact breadth-first projective orbit
used by the cellular exporter.  Selected projective representatives for the
short circuits are recorded in

```text
experiments/projective-points-n49-selected.tsv,
experiments/projective-points-n121-selected.tsv,
experiments/projective-points-n169-shortest.tsv.
```

They are intended for recognizing a symbolic family formula; no such formula
is claimed here.

## Sources

- Avner Ash and Dan Yasaki, *Cohomology of congruence subgroups of
  `SL(3,Z)`*, arXiv:2107.10918, especially the statement that cuspidal
  dimensions at levels `121` and `169` are respectively two and four.
- `TRUE_BOUNDARY_KERNEL_IS_EISENSTEIN_DUAL.md` for `(SCP3)` and `(SCP9)`.
- `TRUE_FUNDAMENTAL_CIRCUIT_PACKET_CERTIFICATE.md` for the general circuit
  certificate and its saturation caveat.
