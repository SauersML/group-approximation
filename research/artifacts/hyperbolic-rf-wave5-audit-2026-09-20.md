# Wave five: other-prime restrictions for the canonical K7 route

Date: 2026-09-20. The order-seven detector from wave four is
established. This document proves a new restriction on the first
abelian quotient covers; it does not provide a detector at another
prime or a uniform theorem over all finite quotients.

## 1. An independence lemma in every characteristic other than seven

Let k be a field of characteristic different from seven containing
a primitive seventh root of unity zeta. For a,b in F7 define the
seven-component vector

```
v_(a,b)(i)=zeta^(a i+b i^2),   i in F7.
```

Any three distinct such vectors are linearly independent over k.
Here coefficients of the exponents, including divisions in F7,
are computed in F7, regardless of the characteristic of k.

Proof. Divide a proposed dependence coordinatewise by one vector.
It becomes a dependence between 1, zeta^P, and zeta^Q for two
distinct nonzero polynomials P,Q of degree at most two, with
P(0)=Q(0)=0. Two distinct such vectors cannot be proportional:
their coordinate at zero is one, and their exponents differ as
functions on F7. Thus every coefficient in the dependence is
nonzero. We may write

```
zeta^Q(i)=alpha+beta zeta^P(i), with alpha,beta nonzero.
```

If P is linear, its phase vector takes all seven distinct seventh
roots. The right side therefore takes seven distinct values, so
Q is linear too. Write Q=rP, with r in {2,3,4,5,6}. The polynomial
T^r-beta T-alpha would then vanish at seven distinct roots,
impossible in degree at most six.

Otherwise write P(i)=a i+b i^2 with b nonzero. Its fibres consist
of a singleton and three pairs, and a pair i!=j satisfies
i+j=-a/b. The displayed dependence forces Q to be constant on
each such fibre. Writing Q(i)=c i+d i^2 gives c=d a/b, hence
Q=rP with r in {2,3,4,5,6}.

Completing the square in F7 shows that the four distinct phase
values of P form the set

```
S=t0 {1,zeta^b,zeta^(2b),zeta^(4b)},
t0=zeta^(-a^2/(4b)).
```

The six pair products of the unscaled four roots are exactly
zeta^(jb), j=1,...,6. Therefore the second elementary symmetric
coefficient of S is

```
e2(S)=t0^2 sum_(j=1)^6 zeta^(jb)=-t0^2 !=0.
```

For r=2 or3, T^r-beta T-alpha has degree less than four and cannot
vanish on S. For r=5 or6, multiply the equation by T^(7-r), using
T^7=1 on S. The resulting polynomial has degree three or two and
again cannot vanish at four roots. For r=4 the same manipulation
gives the quartic

```
1-beta T^4-alpha T^3.
```

If it vanished on S it would be -beta times the monic polynomial
with roots S. Its T^2 coefficient would then be -beta e2(S),
which is nonzero. Its actual T^2 coefficient is zero, a
contradiction. This completes the proof, including characteristics
two and three; the coefficient -t0^2 never vanishes.

## 2. All one-dimensional first cohomology vanishes

Use the marked face presentation already proved in wave four:

```
K=(H0*H1*H2)/<<u_i v_i w_i : i=1,...,6>>.
```

The vertex groups are finite seven-groups. Their abelianizations
have bases U_j,V_j, and the three corner words have abelianized
coordinates i U_j-i^2 V_j/2. Also K_ab=C7^4.

Let chi:K->k^* be a one-dimensional character, first taking k to
contain a primitive seventh root. Any cocycle f:K->k_chi restricts
to a principal cocycle on each vertex by averaging, since its
order is invertible in k. Choose scalars t_j with

```
f(h)=(chi(h)-1)t_j, h in H_j.
```

Put A_i=chi(u_i) and B_i=chi(u_i v_i). Both are quadratic seventh-root
phase vectors, and chi(w_i)=B_i^-1. The cocycle equation on each
face is exactly

```
(t2-t0)+(t0-t1) A_i+(t1-t2) B_i=0.
```

It also holds at i=0, where all corner words are identity. If
1,A,B are distinct vectors, Section 1 forces t0=t1=t2, making
f globally principal.

If A=1 but B is nonconstant, the equation forces t1=t2. The
character on H0 is trivial: the words u1,u2 already span its
abelianization. Hence t0 has no effect on the cocycle, and the
same global primitive works. If A=B but A is nonconstant, the
equation forces t0=t2 and the character on H1 is trivial. If
B=1 but A is nonconstant, it forces t0=t1 and the character on
H2 is trivial. Finally A=B=1 makes the character trivial on all
vertices, and every vertex cocycle is zero. These cases exhaust
the possibilities. Thus H^1(K;k_chi)=0.

For a field without a primitive root, extend scalars to an
algebraic closure. First cohomology and principal-cocycle equations
are finite linear systems from a finite presentation of K, so
faithful scalar extension detects their vanishing. The conclusion
holds over every field of characteristic different from seven.

## 3. Consequences for abelian quotient covers and finite refinements

Let K->A be an abelian quotient and N its kernel. Since K_ab=C7^4,
A is a finite seven-group and N is finitely generated. Over an
algebraic closure k of characteristic different from seven,
k[A] decomposes into its one-dimensional characters. Section 2
therefore implies H^1(K;k[A])=0. Finite-index Shapiro identifies
this group with H^1(N;k), so H1(N;Fell)=0 for every ell!=7.

The same argument in characteristic zero shows that the finitely
generated abelian group N_ab has no free part. It is therefore
finite. The prime-characteristic conclusions show that its order
is a power of seven. This includes N=[K,K], and also every kernel
of a smaller abelian quotient of K.

Suppose a finite image of K is a refinement of K->A, and the
image of N is solvable of order prime to seven. Its abelianization
is a quotient of the seven-group N_ab and also has order prime
to seven, so it is trivial. A solvable perfect group is trivial.
Thus the refinement has trivial kernel. In particular no new
ell-group layer with ell!=7 can be attached directly over any
abelian quotient of K.

This excludes a family of possible affine and solvable detector
constructions beyond the Steinberg restrictions. It leaves
nonabelian seven-group layers, mixed-prime kernels reached after
such layers, and nonsolvable finite quotients untouched. It does
not prove that the canonical class persists at any other prime.

Independent review: the root agent checked the complete proof and
returned PASS, including the fibre argument, all five possible
exponent ratios, the nonzero second symmetric coefficient in
characteristics two and three, the coincident-character cases,
and the scalar-extension and Shapiro steps.

## 4. Two bounded nonabelian seven-quotient sectors

The first class-two exponent-seven quotient of K has Lie dimension
seven. Put A=U0, B=V0, C=U1, D=V1; its central basis is
`T1=[A,C], T2=[B,C], T3=[C,D]`, with `[A,D]=-2 T2`
and the other brackets zero. Its remaining vertex generators are
`U2=-A-C` and `V2=-B-D+T1`. The exact exported structure is
`experiments/hrf-wave5-heisenberg-2026-09-20/class_two.json`.

The script `sectors.py` in that directory constructs representations
over F8, using a primitive seventh root and explicit shift/clock
matrices on a symplectic basis. For a Lie element with coordinates
(p,q,z), the matrix is `zeta^(z-p.q/2) X^p Z^q`, where X shifts
indices by minus p and Z multiplies by zeta raised to q.index.
The radical acts trivially. This convention satisfies the class-two
BCH identity. The script verifies all 49 pairs of Lie basis vectors,
vertex order-seven and commutator relations, and the six face matrix
identities before computing cohomology.

| Central character on (T1,T2,T3) | Module dimension | Face constraint rank | Vertex fixed dimensions | H1 dimension |
|---|---:|---:|---|---:|
| (0,6,0) | 49 | 96 | (1,1,0) | 0 |
| (1,0,0) | 7 | 12 | (1,1,0) | 0 |

The global fixed space is zero in both cases. Since the vertex
groups have odd order, every vertex cocycle is principal over F8.
Writing their three parameters as t0,t1,t2, each face contributes

```
(rho(u_i)-I)t0 + (rho(u_i v_i)-rho(u_i))t1
                 + (I-rho(u_i v_i))t2 = 0.
```

If the stacked face matrix has rank r in dimension d, the resulting
cohomology dimension is `2d-r-sum_j dim(V^Hj)+dim(V^K)`.
All ranks are computed exactly using multiplication in
F2[t]/(t^3+t+1), with no floating point arithmetic.

These are two individual representation sectors. They neither prove
vanishing for the whole class-two cover nor exclude all mixed-prime
finite quotients. They give no new affine quotient in these two
sectors. The result file is `sector_results.json`.

Independent review: the root agent read and replayed `sectors.py`,
verified its finite-field arithmetic, corner formulas, face cocycle
constraints and fixed-primitive subtraction, and returned PASS for
both bounded zero-cohomology results.

## 5. Independent review of the PSL19 characteristic-three square-kernel calculation

The characteristic-three C5-coset projective-generator construction
in `experiments/hrf-wave5-detectors-2026-09-20/c5` was independently
reviewed. The generator script was replayed: its averaging ideal
ranks are 684,1367,2677,3402,3420. The full largest tensor calculation
`tensor_homology.py --only 4 4` was independently replayed to completion
(exit zero, 140.02 seconds), including the input, direct-sum,
intertwining, square-isomorphism and all edge-basis rank checks.
For dimension9801, the three edge dimensions are1961, the three
pair ranks are3917, and the triple rank is5868; the global fixed
space is zero, giving H1 dimension zero. An additional independent
triple-stage replay also returned5868.

The combined result files were checked to contain exactly all25
ordered tensor types, each with a zero cohomology dimension matching
the rank formula. This audit did not rerun all the other24 ranks;
it reviewed their common exact arithmetic implementation and their
recorded outputs. The mathematical projective-generator,
semisimple C5-block, square-isomorphism reduction, cellular rank,
regular-module summand and Shapiro arguments all pass review.

Consequently the completed certificate establishes H1(M;F3)=0 for
the specified PSL2(19)^2 kernel M. Together with the previous F5
calculation, this excludes solvable refinements supported only at
primes three and five. For its central C5 twists, passage from M
preserves H1 with F3 coefficients. The all-finite-quotient problem
and all other prime coefficients remain outside this conclusion.

## 6. GAP p-quotient checkpoint audit

The phase ordering in
`experiments/hrf-wave5-pquotient-2026-09-20/advance.g` was compared
directly with installed GAP4.15.1 `lib/pquot.gi` lines1469–1506.
It matches the native PQuotient loop: define new generators,
compute tails, enforce consistency, lift the epimorphism,
incorporate source relations, and renumber the surviving highest
weight generators. The prepare/lift checkpoint guards carry the
requested class and expected next phase. Final output verifies all
24 source relators in the finite image and verifies centrality of
the marked element before writing the result and workspace.

The group corner word was checked against its Lie convention:
`u^i v^(3 i^2) [u,v]^(3(sigma+3)i^3)` has class-two logarithm
`i U-i^2 V/2+sigma i^3[U,V]/12` modulo seven. Thus the source
presentation agrees with the previously audited canonical marking.
This audit does not repeat the heavy class-ten quotient computation.

The recorded execution is sound. Operational improvements reported
to the root agent: mark the final workspace phase complete so that
a duplicate finish is rejected; reject unrecognized direct GAP
stage values; and clear a restored HRF_SAVE before applying an
optional new save path, so omission cannot overwrite the previous
checkpoint. These do not invalidate the recorded sequence, which
used the correct phases and explicit save paths. Any finite depth
central-order-seven result remains a finite-depth statement only.

The subsequent per-relator checkpoint version of `advance.g` was
also compared with core `LiftEpimorphism` and `EvaluateRelators`.
It calls `TailsInverses` once for each pending class, follows
`RelatorsOfFpGroup` order, maps through the same generator images,
uses the same collector retry loop, and adds the same central tail
vector to the linear relation matrix. The index advances only after
a whole relation has been added; the complete workspace is then
saved. A resume starts at that next index, including the last-index
case where only the phase transition remains. Thus the intended
prepare/lift-batches/finish execution is equivalent to the core.

Using a fresh zero vector per relation is valid: every source
relator already vanishes in the previous quotient, so its lower
coordinates remain zero; core GAP resets only its tail coordinates
for the same reason. An explicit lower-coordinate assertion was
recommended. A further misuse guard was recommended to reject
prepare/all when a checkpoint already has an unfinished lift or
relations phase for that class: the previous-layer length alone
does not detect that condition. No issue was found in the actual
staged sequence, and no duplicate heavy computation was performed.
