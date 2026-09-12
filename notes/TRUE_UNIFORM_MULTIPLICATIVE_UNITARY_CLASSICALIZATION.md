# Multiplicative-unitary compatibility gives a uniform commutation bound

Date: 2026-08-14

## 1. Outcome

The exact classicality theorem in
`TRUE_MULTIPLICATION_TABLE_QUANTUM_CLASSICALIZATION.md` has a
dimension- and table-size-independent quantitative core.

Let `(A,Delta)` be a finite Kac algebra with multiplicative unitary `W`, and
let `Ahat` be its finite dual.  Let `C` be a finite tracial algebra.  Suppose

```text
beta  : A    -> C tensor A,
gamma : Ahat -> Ahat tensor C                            (UMC1)
```

are trace-preserving unital star-homomorphisms.  Put

```text
V =(id tensor beta)W,
V'=(gamma tensor id)W,
epsilon=||V-V'||_2.                                    (UMC2)
```

Then, in the fivefold normalized tracial tensor product,

```text
||V_234 V_135-V_135 V_234||_2 <= 9 epsilon.            (UMC3)
```

The constant does not depend on `dim(A)`, `dim(C)`, or the order of the
underlying finite group.  Expanding `V` in normalized orthonormal bases of
`Ahat` and `A` turns the square of the left side into the normalized mean of
the squared commutators of all coefficient operators.  Thus `(UMC3)` is the
size-uniform averaged classicalization estimate requested in the previous
note.

The theorem does not yet prove nonhyperlinearity.  Its hypotheses ask for
two exact finite-table star-homomorphisms.  The remaining atlas gate is now
precise: construct `beta_n,gamma_n` from the two root-character packets and
bound `(UMC2)` by the fixed cross-root relator defect.

## 2. The two exact tensor identities

The multiplicative unitary satisfies

```text
(Deltahat tensor id)W=W_13 W_23,
(id tensor Delta)W=W_12 W_13.                          (UMC4)
```

Because `beta` is a star-homomorphism, `V` satisfies exactly

```text
(Deltahat tensor id tensor id)V=V_134 V_234.           (UMC5)
```

Because `gamma` is a star-homomorphism, `V'` satisfies exactly

```text
(id tensor id tensor Delta)V'=V'_123 V'_124.           (UMC6)
```

Every map in `(UMC4)--(UMC6)` is trace preserving, hence an `L2` isometry.
All displayed `V` and `V'` terms are unitaries.

Replace `V'` by `V` in `(UMC6)`.  The left side costs at most `epsilon`; the
two-factor product on the right costs at most `2 epsilon` by a unitary
telescope.  Therefore

```text
||(id tensor id tensor Delta)V-V_123 V_124||_2
  <=3 epsilon.                                         (UMC7)
```

No coordinate count occurs in this estimate.

## 3. The five-leg comparison

Apply `Deltahat` to `(UMC7)` and use `(UMC5)` on its two factors.  If

```text
T=(Deltahat tensor id tensor Delta)V,                  (UMC8)
```

then

```text
||T-V_134 V_234 V_135 V_235||_2<=3 epsilon.            (UMC9)
```

Alternatively, apply `Delta` to the exact identity `(UMC5)` and use
`(UMC7)` on each of its two factors.  Two unitary telescopes give

```text
||T-V_134 V_135 V_234 V_235||_2<=6 epsilon.           (UMC10)
```

The triangle inequality compares `(UMC9)` and `(UMC10)`.  Left multiplication
by `V_134^*` and right multiplication by `V_235^*` preserve normalized
Hilbert--Schmidt norm, leaving exactly `(UMC3)`.

The final purely metric implication

```text
distance(T,X Y Z R)<=3 epsilon,
distance(T,X Z Y R)<=6 epsilon
  => distance(Y Z,Z Y)<=9 epsilon                       (UMC11)
```

is formalized source-first as
`middle_swap_distance_le_nine_mul` in
`GroupApproximation/Leavitt/RawWordReynoldsGap.lean`.  No build was run.

## 4. Coefficient form

Choose normalized `L2`-orthonormal bases `(e_i)` of `Ahat` and `(f_j)` of
`A`, and write

```text
V=sum_(i,j) e_i tensor v_(i,j) tensor f_j.             (UMC12)
```

Orthogonality of the four outer tensor legs gives a Parseval identity of the
form

```text
||V_234 V_135-V_135 V_234||_2^2
 =sum_(i,j,k,l)^normalized ||[v_(i,j),v_(k,l)]||_2^2.  (UMC13)
```

Here `sum^normalized` denotes the weights dictated by the normalized bases;
their total coefficient mass is one.  Combining `(UMC3)` and `(UMC13)`
gives

```text
mean_(i,j,k,l) ||[v_(i,j),v_(k,l)]||_2^2
  <=81 epsilon^2.                                     (UMC14)
```

For an ordinary finite group, the `v_(i,j)` are the magic-transport
coefficients after the standard Fourier identifications.  Their asymptotic
commutation produces the whole-map PVM described in `(MQC6)--(MQC8)`.

The normalization in `(UMC13)` matters.  Passing from the averaged bound to
a maximum over all coefficients would reintroduce a factor depending on the
table size and is neither needed nor claimed.  The edge-PVM endpoint and the
robust paired floor are already formulated in total/average error.

## 5. Exact remaining interface

The atlas has the right raw ingredients:

1. finite additive character PVMs, which should define `beta_n`;
2. the paired Fourier/dual packet, which should define `gamma_n`; and
3. cross-root Steinberg commutators, which encode coefficient
   multiplication.

What has not been proved is that these recovered coordinate objects are
simultaneously exact star-homomorphisms and that their multiplicative-unitary
compatibility defect is bounded by the fixed presentation defect with no
dimension- or quotient-size loss.  Establishing

```text
epsilon_n -> 0                                         (UMC15)
```

in `(UMC2)` would now have a complete downstream chain:

```text
(UMC15)
 -> averaged coefficient commutation by (UMC14)
 -> whole-map PVMs by finite PVM rounding
 -> edgewise laws and tree gluing
 -> common latent transports
 -> robust 1/36 contradiction.
```

This is narrower than an arbitrary commutant-lifting theorem.  It asks for
one Fourier-compatible multiplicative-unitary equation between two finite
table homomorphisms, and its analytic amplification constant is already
universal.

The exact-homomorphism input can be weakened further.  It is enough to
construct one unitary which satisfies both coproduct identities
approximately; the direct bound is `3(delta_L+delta_R)`.  See
`TRUE_APPROXIMATE_BICOREPRESENTATION_CLASSICALIZATION.md`.

## Primary source

- P. Kasprzak, P. M. Sołtan, and S. L. Woronowicz,
  *Quantum automorphism groups of finite quantum groups are classical*,
  [arXiv:1410.1404](https://arxiv.org/abs/1410.1404), Theorem 3.1; the two
  expansions leading to equation (3.1) are exactly `(UMC9)--(UMC10)` at zero
  defect.
