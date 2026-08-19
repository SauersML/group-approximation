# A bounded real frame forbids dense bounded-order phase incidence

Date: 2026-08-12

## 1. Outcome

The bounded-real branch of the constant-stabilizer tower now has a second
exact consequence.  The operator estimate in
`FALSE_KAZHDAN_ORBIT_FRAME_OPERATOR_BOUND.md` does not merely exclude real
Fourier concentration.  It also bounds the number of bounded-order
discriminant phases that any one marked-word coordinate can see.

The abstract statement is elementary but decisive.  Let

```text
Q:ell^2(X)->H,       Q delta_x=q_x,
R:ell^2(I)->H,       R delta_j=r_j                         (BFI1)
```

be synthesis operators into a real Hilbert space, with

```text
||Q||<=C,       ||R||<=D.                                (BFI2)
```

Suppose the phase pairings

```text
beta_(xj)=<q_x,r_j> mod Z                                (BFI3)
```

have exponent dividing `M`.  Then every row and every column of the
nonzero phase-incidence relation has size at most

```text
M^2 C^2 D^2.                                            (BFI4)
```

For a selected family of canonical filling classes one has `R=Q P_I`, so
`D<=C` and the bound becomes

```text
M^2 C^4.                                                (BFI5)
```

In particular, order-two canonical filling classes have marked binary row
weight at most `4C^4`.  Therefore the sparse-carry/dense-word hypothesis

```text
a_n/b_n -> 0                                            (BFI6)
```

from `FALSE_BERNOULLI_CARRY_INCIDENCE.md` cannot hold for canonical deck
translates in the bounded-real Kazhdan branch.  More generally, it cannot
hold for any bounded-order latent generator family whose real synthesis
norm is uniformly bounded.

This closes the most direct binary nonlinear escape left after the Kazhdan
orbit-frame theorem.  It does **not** prove a uniform integral decoder.
Arbitrary correlated linear combinations can have an unbounded synthesis
norm even when the canonical orbit synthesis stays bounded, and unbounded
torsion order removes the phase-spacing input in `(BFI4)`.

## 2. The bounded-order phase-incidence theorem

For a class `t+Z in R/Z`, write `ord(t+Z)` for its additive order.

**Theorem 1 (Bessel phase-incidence bound).**  Let `X` and `I` be finite,
let `H` be a real Hilbert space, and let `(BFI1)--(BFI2)` hold.  Assume

```text
M beta_(xj)=0 in R/Z                                    (BFI7)
```

for every `x in X` and `j in I`.  Define

```text
Inc_X(x)={j in I:beta_(xj)!=0},
Inc_I(j)={x in X:beta_(xj)!=0}.                        (BFI8)
```

Then

```text
|Inc_X(x)|<=M^2 C^2 D^2,
|Inc_I(j)|<=M^2 C^2 D^2.                              (BFI9)
```

**Proof.**  If `beta_(xj)` is nonzero and has order dividing `M`, then

```text
dist(<q_x,r_j>,Z)>=1/M.                               (BFI10)
```

In particular `|<q_x,r_j>|>=1/M`.  For fixed `x`, Bessel's inequality in
operator form gives

```text
sum_(j in I)|<q_x,r_j>|^2
 =||R^*q_x||^2
 <=D^2||q_x||^2
 <=C^2D^2.                                           (BFI11)
```

Every member of `Inc_X(x)` contributes at least `1/M^2` to the left-hand
side, proving the first inequality in `(BFI9)`.  Interchanging `Q` and `R`
gives

```text
sum_(x in X)|<q_x,r_j>|^2
 =||Q^*r_j||^2
 <=C^2D^2,                                           (BFI12)
```

and proves the second.  End proof.

The theorem needs neither a group action nor a discriminant lattice.  It is
simply the incompatibility of three simultaneous properties:

1. a bounded synthesis frame;
2. a positive minimum spacing between nonzero phases;
3. unbounded incidence degree.

### Canonical-orbit specialization

If `I subset X` and `r_j=q_j`, then `R=Q P_I`, where `P_I` is the coordinate
inclusion.  Hence `D<=C` and Theorem 1 gives

```text
max_x |{j in I:<q_x,q_j> notin Z}|<=M^2C^4.          (BFI13)
```

If a finite deck group acts transitively and `Q` is equivariant, all full
orbit rows are translates of one another.  Thus `(BFI13)` is a uniform
degree bound on the marked phase Cayley graph, not merely an average bound.

## 3. Application to the binary Bernoulli criterion

Use the notation of `FALSE_RADICAL_FILLING_DISCRIMINANT.md`.  Thus the
canonical minimum real fillings in a regular cover are

```text
q_(n,x)=Q_n delta_x,                                   (BFI14)
```

and their discriminant classes are `c_(n,x)`.  Assume that the intermediate
real filling norms stay bounded.  Theorem `(KOF4)` of
`FALSE_KAZHDAN_ORBIT_FRAME_OPERATOR_BOUND.md` supplies one constant

```text
C_* = max{sup_n Fill_(R,2)(w;H_n), C_J}<infinity      (BFI15)
```

such that

```text
||Q_n||<=C_*                                           (BFI16)
```

for every stage.

Suppose a selected family of canonical classes has order dividing two.
The marked binary incidence matrix from `(BCI7)` is exactly

```text
(B_n)_(x,a)=2<q_(n,x),q_(n,a)> mod 2.                 (BFI17)
```

Indeed, the discriminant pairing represented by the two canonical fillings
is their real inner product modulo `Z`.  The order-two assumption makes the
entry lie in `{0,1/2}` modulo `Z`.  Apply `(BFI13)` with `M=2`:

```text
wt((B_n)_(x,*))<=4C_*^4                               (BFI18)
```

for every row, even after restricting to any subset of canonical deck
translates.

Now let `a_n,b_n` be the carry and word degrees in
`FALSE_BERNOULLI_CARRY_INCIDENCE.md`.  If a positive-weight word row exists,
then `a_n>=1`: otherwise the carry map vanishes on every selected generator,
and injectivity of the discriminant gluing map makes every selected class
zero, contrary to the positive word row.  Equation `(BFI18)` gives

```text
b_n<=4C_*^4,
a_n/b_n>=1/(4C_*^4).                                  (BFI19)
```

Thus `(BCI10)` is impossible.

**Corollary 2 (canonical binary Bernoulli no-go).**  In the bounded-real
branch of the constant-stabilizer Kazhdan tower, no two-torsion subcode
generated by selected canonical deck translates can satisfy the
sparse-carry/dense-word incidence criterion.

The same proof handles noncanonical latent generators provided their glued
real representatives have a uniformly bounded synthesis operator.  If

```text
R_n:ell^2(I_n)->C_2(Y_(K_n),R),
R_n delta_j=r_(n,j),       ||R_n||<=D,                (BFI20)
```

then every order-two word row has weight at most

```text
4C_*^2D^2.                                             (BFI21)
```

Consequently any binary family satisfying `(BCI10)` must have

```text
||R_n||->infinity.                                     (BFI22)
```

So a surviving binary construction must reintroduce an unbounded real frame
through its chosen correlated generators; bounded canonical real geometry
alone cannot support dense marked incidence.

## 4. Total isotropy gives sparse integral autocorrelation

There is a useful endpoint at exponent one.  Suppose the canonical filling
code is totally isotropic, so

```text
<q_x,q_y> in Z                                         (BFI23)
```

for every `x,y`.  Put `G=Q^*Q`.  Since `||G||<=C^2`,

```text
sum_x |G_(xy)|^2=||G delta_y||^2<=C^4.                (BFI24)
```

Every nonzero integer entry contributes at least one.  Hence every row and
column of `G` has at most `C^4` nonzero entries, and every entry has absolute
value at most `C^2`.

For a regular deck action, `G` is convolution by the positive-definite
integer autocorrelation kernel

```text
kappa(a)=<q_1,q_a>.                                    (BFI25)
```

Its support therefore has uniformly bounded cardinality:

```text
|supp(kappa)|<=C^4.                                    (BFI26)
```

This is a finite-propagation **cardinality** statement, not a bounded-radius
statement: the supporting deck elements may escape to infinity.  It reduces
the totally isotropic branch to an integral sparse spectral-factor problem.

## 5. Why sparse integral Gram data are not yet an integral decoder

One cannot conclude from `(BFI23)--(BFI26)` that the minimum fillings are
integral.  The following local example is exact.

Let `A` be any finite group and put

```text
H=ell^2(A;R^3),
v=(1,2,2)/3,
q_a=delta_a tensor v.                                  (BFI27)
```

Then `||v||=1`, the synthesis operator is an isometry, and

```text
<q_a,q_b>=1_(a=b).                                     (BFI28)
```

Thus the Gram matrix is the integral identity and has support one.  Define
the integral local boundary operator

```text
partial(delta_a tensor (x_1,x_2,x_3))
  =(x_1+2x_2+2x_3)delta_a.                             (BFI29)
```

The vector `q_a` is the unique minimum-norm real solution of

```text
partial q_a=3 delta_a,                                 (BFI30)
```

because it is `3(1,2,2)/||(1,2,2)||^2`.  It is not integral, while

```text
z_a=delta_a tensor (1,1,0)                             (BFI31)
```

is an integral solution of the same boundary equation.

Therefore total isotropy plus a bounded real frame does not formally imply
a bounded integral section.  What it does prove is much more specific:
every bounded-order marked phase incidence is uniformly sparse.  To finish
the integral decoder one must additionally exploit the fixed presentation
boundary, the growing discriminant radius, and compatibility of the sparse
spectral factor across the tower.

## 6. Updated residual alternatives

In the explicit bounded-real Kazhdan branch, the canonical order-two
Bernoulli route is closed.  A nonlinear FALSE construction must now use at
least one of the following genuinely new ingredients:

1. discriminant exponent tending to infinity, so the phase spacing in
   `(BFI10)` collapses;
2. correlated latent generators whose real synthesis norms diverge, as in
   `(BFI22)`;
3. a non-product low-energy distribution not controlled by row incidence;
4. a different chart with a growing number of marked coordinate orbits.

To close this explicit FALSE tower in favor of an integral decoder, one
must rule out these four escapes or prove that the sparse integral
autocorrelation normal form `(BFI25)--(BFI26)` has a uniformly bounded
integral spectral factor compatible with the fixed boundary equation.  That
would still be a theorem about this tower, not by itself a proof of the
universal hyperlinear-to-sofic implication.

The companion theorem
`FALSE_BOUNDED_FRAME_PAIRED_CARRY_COLLAPSE.md` further shows that alternatives
2--3 cannot obtain extra existential power merely from the range side of the
paired carry formula: every low-exact-carry/high-word output extracts a
cycle-microscopic/high-word class.  The unresolved object is therefore that
cycle-side class itself.
