# A finite raw-compressor packet produces a properly infinite atlas corner

Date: 2026-08-13

## 1. Outcome

The missing complementary branch in the hard boundary classes is supplied
by the existing rank-four raw swap and comb compressor.  After scalarizing
their explicit matrices through the full depth-two prefix code

```text
C=(00,01,10,11),
```

one hard class-11 pair `(q,l)`, the raw swap `r`, and the comb `u` generate a
properly infinite cylinder projection.  Concretely, put

```text
e  = p_11,
a0 = u* e,
a1 = u* p_001 r e.
```

Exact Leavitt reduction gives

```text
a0 = 11000 11*,        a1 = 111 11*.
```

Therefore

```text
a0* a0 = e,            a0 a0* = p_11000,
a1* a1 = e,            a1 a1* = p_111,
p_11000 p_111 = p_111 p_11000 = 0.                 (RPI1)
```

Thus `e` is equivalent to two orthogonal subprojections.  This is the first
explicit two-child packet in the atlas program.  The previous hard-pair
certificate alone was only one-sided.

The exact arithmetic and projection certificates are archived in
`experiments/atlas-raw-compressor-proper-infinite.json` and reproduced by
`experiments/atlas_raw_compressor_proper_infinite.py`.  The algebraic
two-child conclusion `(RPI1)` is independently formalized in
`GroupApproximation/Leavitt/AtlasProperInfiniteCorner.lean` as
`atlas_properlyInfinite_packet`.

## 2. Scalarized compressor formulas

Let `s_i,t_i` be a binary Leavitt family, `p_i=s_i t_i`, and use the
rank-four matrices already formalized in `RankFourCompressors.lean` and
`RawSwapCompressors.lean`:

```text
       [p0  0  0  s1]             [s0  0  0  p1       ]
Wraw = [ 0  1  0   0],      U  =  [ 0 s0  0  p1 t0    ].
       [ 0  0  1   0]             [ 0  0 s0  p1 t0^2 ]
       [t1  0  0   0]             [ 0  0  0  t0^3    ]
```

Apply

```text
Theta_C((x_ij)) = sum_(i,j) C_i x_ij C_j*.
```

The resulting units are

```text
r = 000 000* + 001 11* + 01 01* + 10 10* + 11 001*,

u = 000 00* + 001 111* + 010 01* + 011 1101*
  + 100 10* + 101 11001* + 11 11000*.              (RPI2)
```

Formula `(RPI2)` immediately yields

```text
u* p_11 = 11000 11*,
r p_11  = 001 11*,
u* p_001 r p_11 = 111 11*.
```

The range words `11000` and `111` are prefix-incomparable, proving `(RPI1)`.

## 3. The two cylinder projections are recovered by the hard pair

Take boundary class `11`, forward rotation zero, and its length-two hard
prefix pair `(q,l)`.  Exact characteristic-two span elimination recovers
both cylinder projections needed above.

For `p_001` the short formula is

```text
p_001 = l* l + q* q* l* l + l* l q q + q* q* l* l q q.  (RPI3)
```

The fixed formula for `p_11` has fifteen monomials of depth at most four;
it is printed in the JSON artifact.  Both identities are rechecked by exact
all-depth prefix expansion.  The certificate space has 210 expanded
monomials and generated rank 77.

Consequently the properly infinite corner is obtained from a finite named
packet:

```text
hard pair q,l + raw swap r + comb u.                 (RPI4)
```

No unbounded collision enumeration or unspecified interior relation is used.

## 4. What this does and does not solve

This closes the algebraic branching gate.  A live matrix obstruction no
longer has to discover a second child or reconstruct the full Leavitt
family: it only has to recover the two fixed projection polynomials `(RPI3)`
and its `p_11` companion in one finite multiplicity algebra.  Once recovered,
`(RPI1)` gives a uniform trace contradiction: a nonzero finite projection
cannot be equivalent to two orthogonal subprojections each having its full
trace.

It is not yet a proof that the atlas group is nonhyperlinear.  The projection
formulas are sums over `F_2`; an approximate complex unitary representation
does not automatically turn XOR sums of group words into projections.
Applying the formulas directly in an ambient finite von Neumann algebra would
also be invalid, since the exact regular representation of the Leavitt group
realizes the group relations while the characteristic-two coefficient
addition is not represented by complex operator addition.

The remaining theorem is now a finite, explicit **projection-recovery gate**:

> In canonical regular-margin matrix models of the finite packet `(RPI4)`,
> the characteristic-two formulas for `p_11` and `p_001` induce, with
> dimension-independent normalized-Hilbert--Schmidt loss, two projections in
> one canonically traced finite multiplicity algebra, and the compressor
> corners converge to the two partial isometries in `(RPI1)`.

This is strictly smaller than the earlier radical-quotient gate.  The target
has two named projections, two named compressor coefficients, and five exact
product identities.

## 5. Reproduction and verification

The exact certificate was run off the local machine with one CPU core:

```text
python experiments/atlas_raw_compressor_proper_infinite.py \
  > experiments/atlas-raw-compressor-proper-infinite.json
```

The Lean file was checked against the existing warm build:

```text
lake env lean GroupApproximation/Leavitt/AtlasProperInfiniteCorner.lean
```

Both checks complete without numerical tolerances.
