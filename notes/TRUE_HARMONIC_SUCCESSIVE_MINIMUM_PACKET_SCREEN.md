# Bounded spanning packets control the harmonic dual systole without overlap

Date: 2026-08-11

## Outcome

The upper-Riesz packet criterion in
`TRUE_HARMONIC_RIESZ_PACKET_CRITERION.md` is stronger than necessary for
the family-level dual-systole bound.  To prove

```text
lambda_1(Q_X^#)>=c>0,                                (HSM1)
```

one does not need an integral basis, a bounded synthesis operator, bounded
Gram row sums, or bounded packet overlap.  It is enough that the real
harmonic space be spanned by elements of the primal lattice `Q_X` whose
individual norms are uniformly bounded.

Equivalently, if the last successive minimum `lambda_r(Q_X)` is uniformly
bounded, then `(HSM1)` holds.  This is the elementary sharp half of the
successive-minimum transference inequality

```text
lambda_r(Q_X) lambda_1(Q_X^#)>=1.                    (HSM2)
```

This substantially weakens the theorem-shaped target suggested by the
rank-seven level-`121` computation.  For denominator control, new harmonic
directions may overlap arbitrarily and may generate a highly nonprimitive
sublattice.  Only bounded norm and real spanning are needed.

The stronger bounded-overlap hypotheses remain relevant for constructing a
uniform **integral lift section**.  This note improves the systole gate, not
the numerator/lift gate.

## 1. Spanning-packet theorem

Let `H` be an `r`-dimensional Euclidean space, let `Q subset H` be a full
lattice, and let

```text
Q^#={u in H:<u,q> in Z for every q in Q}.             (HSM3)
```

**Theorem 1 (bounded spanning packets).**  Suppose there are elements

```text
q_1,...,q_m in Q                                      (HSM4)
```

which span `H` over `R` and satisfy

```text
||q_j||<=A for every j.                               (HSM5)
```

Then

```text
lambda_1(Q^#)>=1/A.                                  (HSM6)
```

**Proof.**  Let `0!=u in Q^#`.  Since the `q_j` span `H`, some
`<u,q_j>` is nonzero.  By `(HSM3)` it is an integer, so

```text
1<=|<u,q_j>|<=||u|| ||q_j||<=A||u||.                 (HSM7)
```

Thus `||u||>=1/A`.  Take the minimum over nonzero `u`.  End proof.

No independence is required.  In particular, an arbitrarily redundant
bounded packet family works.

## 2. Successive-minimum form

The last successive minimum is

```text
lambda_r(Q)
 =inf{A:Q contains r real-linearly independent vectors of norm <=A}.
                                                               (HSM8)
```

Taking those `r` vectors in Theorem 1 gives immediately:

**Corollary 2 (transference lower bound).**

```text
lambda_r(Q) lambda_1(Q^#)>=1.                        (HSM9)
```

This formulation makes three points explicit.

1. The selected packets need not form a `Z`-basis of `Q`.
2. Their generated sublattice may have arbitrarily large index in `Q`.
3. Their supports may overlap arbitrarily.

Indeed, if `Q_0` is the sublattice they generate, then
`Q^# subset Q_0^#`; using the larger primal lattice can only shrink the
dual lattice and improve its first minimum.

## 3. Comparison with the upper-Riesz criterion

For a basis `q_1,...,q_r`, let

```text
T:R^r->H,  T a=sum_i a_i q_i.                        (HSM10)
```

The previous criterion assumes `||T||<=A`, which implies
`||q_i||<=A` and hence `(HSM6)`.  The converse is false: bounded individual
norms only give the crude synthesis estimate

```text
||T||<=sqrt(r) max_i||q_i||,                          (HSM11)
```

and the `sqrt(r)` factor can be real when packets overlap.  Theorem 1 shows
that this factor is completely artificial for the **dual systole**.  It is
not artificial for the section construction, where arbitrary integral
coefficient combinations of lift packets must be controlled.

Thus the two family targets should be separated:

```text
bounded spanning packet norms
       => uniform dual systole;                       (HSM12)

bounded synthesis for compatible lift packets
       => uniform integral section.                  (HSM13)
```

## 4. Projective-chart consequence

For every projective chart `X`, let `Q_X` be the projected harmonic cycle
lattice.  If there is one constant `A` such that `Q_X` contains a real
spanning family of packets of norm at most `A`, then

```text
inf_X lambda_1(Q_X^#)>=1/A.                          (HSM14)
```

Since every nonzero integral spherical template has norm at least one in
the unnormalized integral metric,

```text
inf_X B_X lambda_1(Q_X^#)>=1/A.                      (HSM15)
```

Thus the denominator-collapse mechanism is uniformly excluded even when
the harmonic rank tends to infinity and the packet incidence graph has
unbounded degree.

For the fixed cellular model, the uniform spherical upper bound is
`B_X<=sqrt(52)`.  A stronger chartwise conclusion follows whenever the
spanning packet radius is at most the actual spherical norm `B_X`:

```text
lambda_r(Q_X)<=B_X
  ==> B_X lambda_1(Q_X^#)>=1,                        (HSM16)
```

so that chart contains no nonzero harmonic class below its spherical
localization threshold.

Equation `(HSM16)` gives a particularly concrete exact target.  Instead of
computing SVP in the huge dual lattice, exhibit enough independent primal
projected cycles, each no longer than one spherical template.

## 5. New-real packets and tower saturation

The constant-fibre theorem in
`TRUE_PROJECTIVE_TOWER_SATURATION_REDUCTION.md` says old harmonic directions
pull back isometrically.  Therefore a spanning-packet proof can also be
organized incrementally:

1. pull back the bounded packets spanning the old real harmonic subspace;
2. add bounded packets spanning only the genuinely new real quotient;
3. ignore integral saturation indices for the systole estimate.

The third point follows because Theorem 1 only needs elements of the upper
primal lattice that span the upper real space.  It does not require that
their span be primitive.  Saturation remains essential for integral lift
sections but is invisible to `(HSM14)`.

At level `121`, all seven harmonic directions are new over level `11`.
The sharpened family question is therefore:

> Can the rank-seven space—and its analogues at all later levels—be spanned
> by projected integral cycles of uniformly bounded norm?

This is strictly weaker than constructing the bounded-overlap integral
basis requested previously.  It is compatible with increasing harmonic
rank and with dense overlap among the packets.

## 6. Level-`121` packet certificate

The exact certificate
`experiments/projective-cellular-n121-systole-span.json` exports a basis of
`Q_X^#` with Gram matrix `G`.  The inverse matrix `G^(-1)` is the Gram
matrix of the algebraically dual basis of

```text
(Q_X^#)^#=Q_X.                                       (HSM19)
```

After clearing denominators, exact Gram--LLL gives a unimodular change of
basis in `Q_X` with squared packet norms

```text
0.7573156688...,
0.9947277683...,
1.8795041139...,
2.4918022266...,
2.9858118176...,
3.7821535066...,
5.7961812346....                                     (HSM20)
```

All values and the determinant-one basis change are stored exactly in
`experiments/projective-cellular-n121-primal-packet.json`.  In particular,

```text
lambda_7(Q_X)^2<=5.7961812347<12=B_X^2.              (HSM21)
```

Corollary 2 now proves independently of the dual SVP computation that

```text
12 lambda_1(Q_X^#)^2>=1.                             (HSM22)
```

Thus all seven genuinely new level-`121` harmonic directions admit short
independent primal packets below one spherical template.  The raw algebraic
dual basis is extremely ill-conditioned, with squared norms of orders
`10^1037`--`10^1039`; the unimodular reduction is essential.  The success
shows that this conditioning is a coordinate artifact rather than dangerous
arithmetic.

The same certificate also exports the full reduced Gram matrix.  Its maximum
absolute row sum is

```text
8.7641238749...<12.                                  (HSM23)
```

Since the Gram matrix is symmetric, the Schur/Gershgorin bound gives
`||T||^2<=8.7641238749...` for the packet synthesis operator.  Thus the
level-`121` packet satisfies the stronger upper-Riesz criterion as well as
the successive-minimum criterion.  The exact family screen in
`TRUE_PROJECTIVE_PRIMAL_PACKET_FAMILY_SCREEN.md` finds the same row-sum
success at levels `61,79,89`; `53` is the sole positive-rank tested exception.

## 7. Exact scope

Theorem 1 is a systolic denominator theorem.  It does not choose integral
ambient lifts of vectors in `Q_X^#`.  If `(HSM14)` only gives a positive
constant smaller than `1/B_X`, finitely or infinitely many subthreshold
classes can remain and must be handled by the paired lift formula.  For that
numerator problem the compatible bounded-synthesis section theorem remains
the correct sufficient criterion.

The immediate proof target is nevertheless materially smaller than before:

```text
uniformly bounded real-spanning primal packets,       (HSM17)
```

not

```text
uniform bounded-overlap bases plus dual lift bases.   (HSM18)
```

Establishing `(HSM17)` uniformly would already prove the family-level product bound
highlighted by the level-`121` evidence.
