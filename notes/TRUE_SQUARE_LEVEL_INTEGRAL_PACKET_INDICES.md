# Exact packet indices and an index-two saturation repair

Date: 2026-08-12

## 1. Outcome

The square-level cellular packets at levels `121` and `169` now have exact
integral index certificates.  Write `K` for the primitive integral cycle
lattice, `S_sat` for the saturation of the cellular boundaries in `K`, and

```text
Q=K/S_sat.                                                   (SPI1)
```

If `B` is the selected independent boundary-row lattice and `C` is a
rationally full packet, then

```text
[K:<B,C>]=[S_sat:B] [Q:P_H<C>].                              (SPI2)
```

Sparse unit elimination followed only by a tiny residual column HNF gives
the three exact indices in `(SPI2)` without constructing a basis of `K`.
The results are

```text
level 121: [S_sat:B]=8,    [K:<B,C>]=8,
           [Q:P_H<C>]=1;

level 169: [S_sat:B]=3136, [K:<B,C>]=6272,
           [Q:P_H<C>]=2.                                  (SPI3)
```

Thus the original level-`121` packet is already an integral basis, while the
original level-`169` packet misses exactly one parity class.  This also
explains why the nonunit residuals seen by the direct solvers must not be
identified with harmonic obstructions: at level `121` all index `8` lies in
the chosen presentation of the boundary lattice, and the harmonic packet
index is one.

The level-`169` defect is now repaired.  Among the sixteen exact cycle
records, record `15` replacing selected record `3` has projected index `7`.
The corrected cycle

```text
c_new=c_15-3c_3                                              (SPI4)
```

has replacement determinant one.  The selected packet

```text
[0,2,1,16,7,5,11,6,8,9,13,14]                              (SPI5)
```

therefore projects to a `Z`-basis of all twelve directions of `Q_169`.
The new record has squared norm `824`, support `391`, and maximum coefficient
`6`.  The full repaired packet has maximum absolute Gram row sum `1018`.

## 2. Multiplicative packet-index theorem

Let `K` be a free abelian group, let `S subset K` be primitive, and put
`Q=K/S`.  Let `B subset S` have finite index in `S`, and let `C subset K`
be a free subgroup whose projection to `Q` is injective with finite-index
image.  Equivalently, `C` is an integral packet rationally complementary to
`S`.

**Theorem 1.**  The index factors as

```text
[K:B+C]=[S:B] [Q:bar(C)].                                   (SPI6)
```

**Proof.**  Since `B+C` maps onto `bar(C)` under `K -> Q`, injectivity of the
projection on `C` gives `(B+C) intersect S=B`.  The
quotient map gives an exact sequence

```text
0 -> S/B -> K/(B+C) -> Q/bar(C) -> 0.                       (SPI7)
```

Taking orders proves `(SPI6)`.  Equivalently, choose bases adapted to the
rational splitting `K_Q=S_Q directSum C_Q`; the determinant is block
triangular and its two diagonal determinants are the displayed indices.
End proof.

For an independent integral row matrix `A`, the index of its row lattice in
its saturation is the gcd of its maximal minors.  Content-normalized unit
elimination preserves this index except that dividing a residual row of
content `d` records a factor `d`.  When no unit remains, the determinant of
the square head of the column HNF records the remaining index.  This is the
exact procedure used in

```text
experiments/sl3_projective_packet_index_sparse.py.           (SPI8)
```

The level-`169` factorization is

```text
3136=2^6 7^2,       6272=2^7 7^2,                           (SPI9)
```

so their quotient is exactly two.

## 3. Index-two correction lemma

The repair `(SPI4)` is an instance of a general elementary lemma.

**Lemma 2 (one-row index-two repair).**  Let
`C=(c_1,...,c_r)` be an ordered full-rank packet in a rank-`r` lattice `Q`
with index two.  Fix `j`, and suppose replacing `c_j` by `x` gives a
full-rank packet of odd index `m`.  Then one of

```text
x-((m-1)/2)c_j,       x+((m-1)/2)c_j                       (SPI10)
```

gives a basis of `Q`.

**Proof.**  In any oriented basis of `Q`, let `a` be the signed determinant
of `C` and `b` the signed determinant after replacing `c_j` by `x`.  Thus
`a=+-2` and `b=+-m`.  Determinant is linear in the replacement row, so

```text
det(x+k c_j)=b+k a.                                        (SPI11)
```

For one of the two signs in `(SPI10)`, the right side is `+1` or `-1`.
That packet is therefore unimodular.  End proof.

At level `169`, `m=7`; the successful sign is `k=-3`, yielding `(SPI4)`.
This lemma is useful at family scale: an index-two packet does not require a
global Smith basis.  It suffices to find one rational replacement of odd
index, then make one bounded integral correction if that odd index is
bounded.

## 4. Why raw mod-two homology is not enough

At level `169`, rational `H_2` has dimension `12`, whereas the computed
mod-two homology space used by the screen has dimension `16`.  Universal
coefficient torsion therefore contributes extra binary directions.  Indeed,
the original index-two packet can have signature rank `12` in this enlarged
space without spanning `Q/2Q`.

Consequently the reliable workflow is

```text
binary screen
 -> exact rational-rank check
 -> exact integral packet index
 -> determinant correction.                               (SPI12)
```

The first two failed runs exposed this distinction: a binary-full candidate
could be rationally dependent, and another could remain of even free index.
The final certificate records both kinds of rejection rather than treating
them as harmonic repairs.

## 5. Qualitative dual lifting is now automatic

The index-one conclusion has a useful consequence which does not require a
second normal-form computation.

**Proposition 3 (integral packet-dual extension).**  Let `E=Z^N`, let
`K=ker(d:E->F)` for a homomorphism to a free abelian group, let `S subset K`
be primitive, and suppose `c_1,...,c_r` project to a basis of `Q=K/S`.
Then there are integral ambient covectors `z_1,...,z_r in Hom(E,Z)` such that

```text
z_i(S)=0,             z_i(c_j)=delta_(ij).              (SPI13)
```

**Proof.**  The dual coordinate map on `Q` composes with `K->Q` to an
integral functional on `K` satisfying `(SPI13)` there.  The kernel `K` is
primitive in `E`, because `E/K=im(d)` is a subgroup of the free group `F`
and is therefore free.  Hence `K` is a direct summand of `E`, so every
integer functional on `K` extends to one on `E`.  End proof.

For the repaired level-`169` packet this proves, exactly and without a
two-primary qualification, that all twelve packet-dual harmonic classes
have integral ambient lifts.  Thus the earlier parity defect was only a bad
choice of primal packet.  What remains quantitative is not existence of a
lift but construction of extensions whose synthesis norm is uniformly
controlled over the family.  Generic HNF extensions can have enormous
coefficients and provide no evidence about that norm.

There is also a precise reason that reducing such an HNF witness only by raw
coboundary rows can fail badly.

**Proposition 4 (the extension fiber is the saturated annihilator).**  In the
notation of Proposition 3, identify `Hom(E,Z)` with `Z^N`.  If `z_0` is one
ambient extension of a fixed functional on `K`, then all its extensions are

```text
z_0 + Ann_Z(K),
Ann_Z(K)=Row_Q(d^T) intersect Z^N
        =Sat(Row_Z(d^T)).                                (SPI14)
```

The raw row lattice `Row_Z(d^T)` can have finite index in `(SPI14)`.  More
precisely, if `I=im(d) subset F`, restriction gives an exact sequence whose
cokernel is

```text
Hom(I,Z)/res(Hom(F,Z)) ~= Ext^1(F/I,Z),                 (SPI15)
```

and hence has the same finite invariant factors as the torsion of `F/I`.

**Proof.**  A difference of two extensions vanishes on `K`, hence factors
uniquely through the free quotient `E/K~=I`; this identifies the kernel of
restriction `Hom(E,Z)->Hom(K,Z)` with `Hom(I,Z)`.  Pulling back along `d`
identifies it inside `E^*` with the integral points in the rational row
space of `d`, proving `(SPI14)`.  Applying `Hom(-,Z)` to
`0->I->F->F/I->0` gives `(SPI15)`.  End proof.

This changes the quantitative computation.  Greedy subtraction of rows of
`d_2^T` explores only `Row_Z(d_2)` and can miss exactly the torsion-index
directions in `(SPI15)`.  The correct short-lift problem is CVP in the
saturated annihilator `(SPI14)`.  The enormous coefficients of the first
generic level-`169` HNF extensions therefore do not indicate geometric
growth; before drawing that conclusion one must reduce in the full
saturated fiber.

For a chain complex, this quotient has a more intrinsic description.

**Proposition 5 (the missing extension directions are first homology).**
For free integral chains

```text
C_2 --d_2--> C_1 --d_1--> C_0,
```

there are canonical identifications

```text
Sat(Row_Z(d_2^T))/Row_Z(d_2^T)
 ~= Ext^1(coker(d_2),Z)
 ~= Ext^1(H_1,Z).                                      (SPI16)
```

In particular, this finite group has the same invariant factors as the
torsion subgroup of `H_1`.

**Proof.**  Proposition 4 gives the first identification.  There is an exact
sequence

```text
0 -> H_1 -> coker(d_2) -> im(d_1) -> 0.                (SPI17)
```

The last term is free, so `(SPI17)` splits as an extension of abelian groups
and contributes no `Ext^1(-,Z)`.  End proof.

This completely localizes the extra arithmetic: the short-extension solver
must add precisely the torsion directions of integral `H_1`, not saturate an
unrelated enormous lattice blindly.

At level `169`, `rank(d_2)=2530`.  Exact modular ranks are

```text
rank_(F_l)(d_2)=2530,   l=2,3,5,7,
rank_(F_13)(d_2)=2529.                                (SPI18)
```

Thus the visible defect is not binary: it is one-dimensional at the level
prime `13`.  The unique dependence among a suitable `2530`-row rational
basis modulo `13` gives an exact divided combination `v_13` satisfying

```text
13 v_13 in Row_Z(d_2^T),
rank_(F_13)(Row_Z(d_2^T)+Z v_13)=2530.                 (SPI19)
```

Consequently adjoining `v_13` removes the entire `13`-primary saturation
defect.  The vector is concrete and modest: support `1533`, squared norm
`2103`, and maximum coefficient `3`.  This does not by itself exclude
torsion at untested primes, but it proves that the level-`169` correction is
one explicit row rather than a full Smith-basis problem.

## 6. Meaning for TRUE

The level-`169` chart is the second square-level chart with growing harmonic
rank, and its apparent parity obstruction is now finite and explicitly
repairable.  Together with the determinant-one level-`121` packet, this is
new evidence for the family statement needed by TRUE:

> construct rationally local packets whose integral indices and odd
> replacement determinants are uniformly bounded, then apply Lemma 2 and
> construct uniformly bounded packet-dual lifts.

The present result proves the integral-basis and qualitative dual-lift parts
of that program at levels `121` and `169`; it does not yet establish
uniformity over all levels.  The repaired level-`169` packet has a larger row
than the original short packet, so the next theorem-shaped target is a local
construction or range reduction giving its packet-dual extensions a useful
norm bound.

## 7. Certificates

```text
experiments/projective-cellular-n121-packet-index.json
experiments/projective-cellular-n169-packet-index.json
experiments/projective-cellular-n169-cycle-boundary-saturated.json
SHA-256 b9f37304009e64acb829c6c4da5f7f3f7dcbce9996f88b9c8794b147ee90e483

experiments/projective-cellular-n169-modular-small.json
SHA-256 ceeb8bb2a3dd743ceb3a22731709844d908326690ddd80719397e2a69fcb87d1

experiments/projective-cellular-n169-d2-saturation-p13.json
SHA-256 8e87f3ce7a68a7162cfd2ce4b77c376f31f61f391ff68f0d0efc5e011828e19a

experiments/sl3_projective_packet_index_sparse.py
experiments/sl3_projective_packet_saturate.py
experiments/sl3_projective_row_saturation_direction.py
```

The repaired certificate contains all exact cycle coordinates, every
rejected replacement profile, the successful index-seven profile, the
index-one corrected profile, and the full packet Gram matrix.
