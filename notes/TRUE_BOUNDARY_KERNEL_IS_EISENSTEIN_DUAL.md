# The absolute boundary kernel is the dual degree-two Eisenstein lattice

Date: 2026-08-12

## Outcome

The five-dimensional boundary kernel isolated at level `121` has a canonical
cohomological identity. Let `M` be an oriented compact five-manifold with
boundary (or the rational Borel--Serre orbifold obtained from an arithmetic
quotient), and put

```text
E^2(M)=im(H^2(M;Q)->H^2(partial M;Q)).                       (BED1)
```

This is the degree-two Eisenstein image. The boundary intersection pairing
makes `E^2(M)` a Lagrangian subspace of `H^2(partial M;Q)`, and induces a
canonical isomorphism

```text
H^2(partial M;Q)/E^2(M) ~= E^2(M)^*.                         (BED2)
```

Combining `(BED2)` with the pair sequence and the Lee--Schwermer boundary
theorem gives

```text
0 -> E^2(M)^* -> H_2(M;Q) -> H_cusp^3(M;Q) -> 0.             (BED3)
```

Thus the “boundary packet” problem is exactly the dual degree-two
Eisenstein packet problem. It is not an amorphous extra part of absolute
homology.

At level `121`,

```text
dim H_2=7,       dim H_cusp^3=2,       dim E^2=5.             (BED4)
```

The seven harmonic directions are therefore the extension of a rank-two
cuspidal quotient by the dual of a rank-five Eisenstein image.

The first discriminating small square-level computation confirms the same
structure:

```text
dim H_2(Gamma_0(49);Q)=1,
dim H_cusp^3(Gamma_0(49);Q)=0,
dim E^2=1.                                                   (BED4a)
```

There is also an integral refinement. For a torsion-free quotient, let

```text
L=H^2(partial M;Z)/torsion,
E=im(H^2(M;Z)/torsion -> L),
E_sat=L intersect (E tensor Q).                              (BED5)
```

Then `E_sat` is a primitive Lagrangian and

```text
L/E_sat ~= E_sat^*,                                         (BED6)
0 -> E_sat/E -> L/E -> E_sat^* -> 0.                        (BED7)
```

Consequently the finite saturation defect `E_sat/E` is precisely the extra
integral denominator layer hidden by the rational splitting. This is the
boundary counterpart of the paired-discriminant gluing already present in
circle repair.

It is not an independent source of torsion. The integral pair sequence gives
a canonical injection

```text
E_sat/E -> Tor(H^3(M,partial M;Z)/delta Tor H^2(partial M;Z))
        <-< Tor H_2(M;Z).                                   (BED7a)
```

Here the last notation means “is a subquotient of.” In particular, if
`H_2(M;Z)` is torsion-free, then `E=E_sat`: the degree-two Eisenstein
restriction image is automatically primitive.

## 1. The middle boundary image is Lagrangian

Write

```text
r_q:H^q(M;Q)->H^q(partial M;Q),
delta_q:H^q(partial M;Q)->H^(q+1)(M,partial M;Q).             (BED8)
```

The oriented four-manifold `partial M` has the nondegenerate intersection
pairing

```text
<x,y>_partial = <x cup y,[partial M]>,
H^2(partial M;Q) x H^2(partial M;Q) -> Q.                   (BED9)
```

Compatibility of boundary and Lefschetz pairings says, up to the irrelevant
orientation sign,

```text
<r_2(a),x>_partial = <a,delta_2(x)>_M.                       (BED10)
```

First take `x=r_2(b)`. Exactness gives `delta_2 r_2(b)=0`, hence `(BED10)`
shows that `E^2(M)` is isotropic.

Conversely, suppose `x` annihilates `E^2(M)`. Then the right side of
`(BED10)` vanishes for every `a in H^2(M;Q)`. The Lefschetz pairing

```text
H^2(M;Q) x H^3(M,partial M;Q) -> Q                          (BED11)
```

is nondegenerate, so `delta_2(x)=0`. Exactness gives
`x in im(r_2)=E^2(M)`. Therefore

```text
E^2(M)^perp=E^2(M).                                         (BED12)
```

The map

```text
H^2(partial M;Q)/E^2(M) -> E^2(M)^*,
x+E^2(M) |-> (e |-> <x,e>_partial)                          (BED13)
```

is now injective by `(BED12)`. Both sides have the same dimension because a
Lagrangian has half the dimension of a nondegenerate space. Hence `(BED13)`
is the canonical isomorphism `(BED2)`.

This argument is purely topological. It is the degree-two, five-dimensional
instance of the general statement that complementary boundary restriction
images are mutual annihilators. Bajpai--Harder--Horozov--Moya Giusti record
the same maximal-isotropic Eisenstein principle in their Poincare-duality
description of boundary cohomology.

## 2. Identification inside absolute H2

The pair sequence contains

```text
H^2(M) -> H^2(partial M) -> H^3(M,partial M)
  -> H^3(M) -> H^3(partial M).                              (BED14)
```

Therefore `(BED2)` identifies the kernel of the middle map with `E^2(M)^*`.
For a five-manifold, Lefschetz duality gives

```text
H^3(M,partial M;Q) ~= H_2(M;Q).                              (BED15)
```

For the `SL_3` Borel--Serre quotient, Lee--Schwermer identify the kernel of
the last restriction in `(BED14)` with interior degree-three cohomology, and
interior degree three with cuspidal degree three. Exactness now turns
`(BED14)` into `(BED3)`.

Equation `(BED3)` refines the earlier boundary/cuspidal split. The left term
is not merely a cokernel with unknown structure: it is canonically dual to
the degree-two Eisenstein restriction image.

## 3. Integral saturation and discriminant gluing

Assume first that `M` is a genuine compact oriented five-manifold. The free
lattice `L` in `(BED5)` has a unimodular integral intersection form. The
rational proof shows that `E_sat tensor Q` is Lagrangian. Primitivity of
`E_sat` and unimodularity of `L` imply that every integral functional on
`E_sat` extends to `L`. Hence

```text
L -> E_sat^*,       x |-> <x,->                              (BED16)
```

is surjective. Its kernel is `E_sat^perp=E_sat`, proving `(BED6)`.

Since `E subset E_sat subset L`, the quotient sequence gives `(BED7)`.
The finite group `E_sat/E` measures failure of the actual restriction image
to be primitive. Even if bounded packets are known for the rational
Eisenstein space, a uniform circle-repair theorem must still control this
finite group and the metric norm of a section of `(BED7)`.

There is an exact torsion localization of this group. Write

```text
A=H^2(M;Z),
B=H^2(partial M;Z),
C=H^3(M,partial M;Z),
T_B=Tor(B).                                                (BED16a)
```

The pair sequence is exact at `B`:

```text
A --r--> B --delta--> C.                                  (BED16b)
```

The map `delta` descends to

```text
delta_bar:B/T_B -> C/delta(T_B).                          (BED16c)
```

Its kernel is exactly `E`. Indeed, if `delta(b)=delta(t)` for some
`t in T_B`, then `b-t in ker(delta)=im(r)`, so the class of `b` in
`B/T_B` lies in `E`; the converse is immediate. Hence

```text
(B/T_B)/E -> C/delta(T_B)                                 (BED16d)
```

is injective. The torsion subgroup of the source is exactly `E_sat/E`.
Because `delta(T_B)` is torsion, the torsion subgroup of the target is a
quotient of `Tor(C)`. Therefore

```text
E_sat/E embeds in Tor(C)/delta(T_B).                       (BED16e)
```

Integral Lefschetz duality identifies `C` with `H_2(M;Z)`, proving
`(BED7a)`. Two useful consequences are immediate:

```text
exp(E_sat/E) divides exp Tor H_2(M;Z),
Tor H_2(M;Z)=0  =>  E=E_sat.                              (BED16f)
```

Thus boundary saturation introduces no new prime or exponent beyond
absolute degree-two homology torsion. In the projective program it belongs
to the existing derived primary gate, not to the free harmonic packet gate.

For arithmetic quotients with torsion, the rational statement follows after
passing to a torsion-free normal finite cover and taking finite-group
invariants. The integral assertion must retain stabilizer primes and transfer
indices; it should not be imported from `(BED7)` without those corrections.
Those corrections are exactly the derived primary sectors already isolated
in the projective cellular model.

## 4. Consequences for the family strategy

The corrected TRUE-side division of labor is now:

1. **Cuspidal quotient.** Use unimodular modular-symbol closing to bound the
   two-dimensional interior quotient when it is present.
2. **Eisenstein kernel.** Construct bounded degree-two Eisenstein restriction
   packets; their boundary intersection duals give the absolute kernel.
3. **Integral gluing.** Control the already-existing `H_2` primary torsion,
   which contains the saturation group by `(BED16e)`, and bound the metric
   section coupling the Eisenstein and cuspidal pieces.

This is substantially sharper than asking for arbitrary boundary-stratum
packets. Degree-two Eisenstein cohomology is assembled from the maximal
parabolic modular-curve faces and their incidence along minimal faces, so
the next literature and chain-level audit has a specific object to target.

The square-level dimension is now a theorem, not merely a four-level pattern.
For every odd prime `p`, Lee--Schwermer's exact boundary module, descended
through the maximal-face stabilizers computed by Ash--Yasaki, gives

```text
dim E^2(Gamma_0(p^2,3))
 = dim S_3(Gamma_1(p))
 = dim S_2(Gamma_0(p^2))-dim S_2(Gamma_0(p)).                (BED17)
```

For `p>=5` this is `(p-1)(p-5)/12`; for `p=3` it is zero.  More
structurally, the degree-two boundary is the direct sum of the weight-three
cusp spaces on the two middle maximal faces, and the Eisenstein image is the
graph of the constant-term intertwining operator between them.  Thus the
remaining square-level packet problem is one `S_3(Gamma_1(p))` integral
modular-symbol lattice plus one scattering graph.  The proof is in
`TRUE_SQUARE_LEVEL_EISENSTEIN_GRAPH.md`.

The exact charts at levels `9,25,49,121` give dimensions `0,0,1,5`, in
agreement with `(BED17)`. In particular, level `49` was the first case where
the theorem predicts a nonzero space without a cuspidal contribution, and
its exact rank is one as predicted.

The exact level-`49` complex has dimensions

```text
Q^139 <- Q^356 <- Q^320 <- Q^110
```

and boundary ranks `(138,218,101)`, so its homology dimensions are
`(1,0,1,9)`. Three modular fields `101,1009,10007` give the same ranks, and
the exact rational analyzer constructs the rank-one harmonic lattice. Its
shortest nonintegral `Q^#` class has norm

```text
0.335966093411573...,
```

which is above the spherical threshold `1/sqrt(28)`. Thus this new
Eisenstein direction is chart-safe as well as structurally informative.

Certificates:

```text
experiments/projective-cellular-n49-summary.json
SHA-256 3c3727e4df6d0ce2018ece91670e782879b2b5568942d57223b900598a3ffadc,

experiments/projective-cellular-n49-modular-screen.json
SHA-256 d1ca1f99ca43b610b92cc28fc10925893529bc06835a747b28ed76c3adac1881.
```

## Sources

- Jitendra Bajpai, Gunter Harder, Ivan Horozov, and Matias Victor Moya Giusti,
  [*Boundary and Eisenstein cohomology of SL3(Z)*](https://doi.org/10.1007/s00208-020-01976-9),
  especially Section 6.2 on Poincare duality and maximal isotropic
  Eisenstein images.
- Avner Ash and Dan Yasaki,
  [*Cohomology of congruence subgroups of SL(3,Z)*](https://arxiv.org/abs/2107.10918),
  Section 7 for the Lee--Schwermer boundary theorem and Section 12.4 for
  level `121`.
- Ronnie Lee and Joachim Schwermer,
  [*Cohomology of arithmetic subgroups of SL3 at infinity*](https://doi.org/10.1515/crll.1982.330.100),
  Theorem 2.4 and Section 6.1 for the exact degree-two boundary module and
  its scattering graph.
- `TRUE_ABSOLUTE_H2_INTERIOR_BOUNDARY_SPLIT.md` for the first rational split.
