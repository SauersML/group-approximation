# Equivariant transition PVMs coarsen to whole response maps

Date: 2026-08-14

## 1. Outcome

The gap between per-source extension outcomes and whole response maps closes
whenever the transition PVM is equivariant under the paired translations
recovered in `TRUE_NESTED_COMMUTATORS_RECOVER_PAIRED_TRANSLATIONS.md`.

On one free translation orbit, pull every source-conditioned transition PVM
back to one base fiber.  Exact equivariance makes all pulled-back PVMs equal.
Each base outcome then determines one response at every source by
translation, and orbit-summing its projections produces a PVM indexed by
whole equivariant maps.

Approximate equivariance has a cardinality-free version.  If the mean total
squared discrepancy of the pulled-back PVMs is `epsilon`, averaging produces
a POVM whose total non-idempotence is at most `2 epsilon`.  De la Salle
rounding then gives one base PVM with total squared error below
`18 epsilon`; transporting it around the orbit gives an exact whole-map PVM.
No factor depends on the orbit size, response alphabet, or matrix dimension.

This result closes the common-map extraction **after source and target have
been placed in the same finite paired orbit**.  A literal covariance audit
still proves equivariance, but equivariance alone permits a proper map into a
larger target orbit.  The exact direct-sum countermodel is recorded in
`FALSE_EQUIVARIANT_WHOLE_MAPS_ALLOW_RECTANGULAR_ESCAPE.md`.  The remaining
theorem must therefore combine raw/comb covariance with same-orbit closure.

## 2. Exact orbit construction

Let a finite group `K` act freely and transitively on a finite source set
`X`.  Fix `x0 in X`, so every `x` has a unique form `k x0`.  Let `Y` be a
finite `K`-set.  Suppose a finite-dimensional Hilbert space has a source PVM

```text
(P_x)_(x in X),                                      (ETM1)
```

and unitaries `(D_k)_(k in K)` satisfying

```text
D_k P_x D_k* = P_(k x).                              (ETM2)
```

Inside every source block, suppose there is a response PVM

```text
(A_(x,y))_(y in Y),
A_(x,y)<=P_x,             sum_y A_(x,y)=P_x.         (ETM3)
```

Assume exact equivariance:

```text
D_k A_(x,y) D_k* = A_(k x,k y).                     (ETM4)
```

For `y in Y`, define its equivariant response map

```text
f_y(k x0)=k y.                                       (ETM5)
```

Freeness on `X` makes `(ETM5)` well-defined.  Distinct `y` can determine the
same map only when the `K`-action on `Y` has a kernel; this causes no problem,
because the corresponding projections may simply be summed.

Define

```text
Q_y=sum_(k in K) D_k A_(x0,y) D_k*.                 (ETM6)
```

The summands for different `k` lie under the orthogonal projections
`P_(k x0)`.  Hence every `Q_y` is a projection, the `Q_y` are pairwise
orthogonal, and

```text
sum_y Q_y=1                                         (ETM7)
```

on the orbit carrier.  Equations `(ETM4)--(ETM6)` give

```text
A_(x,z)=sum_(y:f_y(x)=z) P_x Q_y.                   (ETM8)
```

After merging equal maps, `(Q_y)` is therefore a PVM indexed by whole
response maps.  It recovers every original source-conditioned response PVM
as a deterministic marginal.

For several source orbits, perform `(ETM6)` on each orbit and take the direct
sum.  Orbit size and multiplicity may vary; the construction is exact on
every summand.

## 3. Why internal multiplicity does not matter

No irreducibility assumption occurs in `(ETM1)--(ETM8)`.  Each
`A_(x0,y)` may have arbitrary rank, and each `D_k` may contain an arbitrary
unitary between equal-rank multiplicity blocks.  The same physical `D_k`
appears both in the definition of `Q_y` and in the equivariance law, so the
internal unitary cancels from `(ETM8)`.

This is the precise gain from using the named commutators

```text
D_b=[x_23(1),x_34(b)],
C_a=[x_12(a),x_23(1)]                                (ETM9)
```

rather than choosing an abstract regular-representation gauge.  On a fixed
long-root character sector, `(ETM9)` supplies the physical translations of
the outer character PVMs.

## 4. Approximate orbit averaging

It is enough to state the quantitative step in one base block.  Pull the
response PVM at `k x0` back along `D_k` and relabel its outcomes by the
inverse `K`-action.  This gives a PVM

```text
B^k=(B^k_y)_(y in Y)                                 (ETM10)
```

in `P_(x0) M P_(x0)`.  Exact equivariance says `B^k=B^e`.  Suppose instead

```text
epsilon
 =(1/|K|) sum_k sum_y ||B^k_y-B^e_y||_2^2.          (ETM11)
```

Put

```text
C_y=(1/|K|)sum_k B^k_y.                              (ETM12)
```

Then `(C_y)` is a POVM.  The elementary variance identity for Hilbert-space
vectors gives

```text
sum_y tau(C_y-C_y^2)
 =(1/(2|K|^2))sum_(k,l,y)||B^k_y-B^l_y||_2^2.       (ETM13)
```

Using

```text
||B^k_y-B^l_y||_2^2
 <=2||B^k_y-B^e_y||_2^2
   +2||B^l_y-B^e_y||_2^2                            (ETM14)
```

in `(ETM13)` yields

```text
sum_y tau(C_y-C_y^2)<=2 epsilon.                    (ETM15)
```

De la Salle's cardinality-free orthogonalization theorem therefore produces
a PVM `(R_y)` in the base block with

```text
sum_y||C_y-R_y||_2^2 <18 epsilon.                   (ETM16)
```

The exact variance decomposition also gives

```text
(1/|K|)sum_(k,y)||B^k_y-C_y||_2^2
 =sum_y tau(C_y-C_y^2)
 <=2 epsilon.                                       (ETM17)
```

Combining `(ETM16)--(ETM17)` with the squared triangle inequality gives the
safe total estimate

```text
(1/|K|)sum_(k,y)||B^k_y-R_y||_2^2 <40 epsilon.      (ETM18)
```

Transport `(R_y)` around the source orbit exactly as in `(ETM6)`.  The
result is an exactly equivariant whole-map PVM whose source-conditioned
marginals differ from the original family by total mean squared error below
`40 epsilon`.  The constant is universal.

One can improve `40`, but no later step needs it: only convergence to zero
and independence from all finite alphabet sizes matter.

## 5. Covariance supplies equivariance

Let `U` be the actual compressor transition, let `D_k` be a source
translation, and let `E_(phi(k))` be the corresponding target translation.
Assume

```text
U D_k U* = E_(phi(k)).                               (ETM19)
```

For exact source and target character PVMs `(P_x)` and `(S_y)`, the intrinsic
transition projections are

```text
A_(x,y)=P_x U* S_y U P_x.                           (ETM20)
```

The source and target shift identities, together with `(ETM19)`, give

```text
D_k A_(x,y) D_k*=A_(k x,phi(k)y).                   (ETM21)
```

Thus the equivariance required in `(ETM4)` is not a new choice of gauge.  It
is an algebraic consequence of covariance of the **same physical
transition unitary** with the named paired translations.

In normalized-Hilbert--Schmidt coordinates, a three-factor telescope bounds
the mean discrepancy in `(ETM21)` by the root-shift defects, compressor
translation-covariance defect, and transition-PVM rounding error.  Averaging
over the complete finite translation packet introduces no cardinality loss;
choose the packet growth slowly relative to the microstate accuracy.

## 6. Interaction with the exact additive countermodel

The model in
`FALSE_EXACT_JOINT_COMPRESSOR_HAS_MAXIMAL_FIBER_VARIANCE.md` has `U=1` and
maximal binary variance inside every restriction fiber.  It also satisfies
equivariance.  The present theorem explains rather than contradicts that
example: its fine transition is the uniform classical mixture of all
affine sections of the restriction map.  A branch bit is not a function of
the coarse source character, but it **is** a function of the latent affine
section and the source character.

That is exactly the qualification required by the robust paired-quotient
floor, which permits a common classical mixture of whole maps.  Pure
additive covariance permits every section and has no contradiction.  The
Leavitt diagonal-one/cross-zero table is the additional condition which
should make every such common mixture pay the fixed `1/36` error.

## 7. Remaining literal audit

The operator theorem is complete, but its application still requires four
specific group-word covariance statements.  For the two outer-root
translation families `(ETM9)`, verify that the raw/comb words implementing

```text
a |-> a t_i,             b |-> s_j b                (ETM22)
```

carry each named middle-root commutator to the commutator with the
transported coefficient, up to the root-index routing already proved in
`RawSwapCompressors.lean`.  The comb covariance for the corner map follows
formally by conjugating both entries of a commutator.  The branch-`1` raw
word changes root indices, so those target translations must be written in
the routed last-row/last-column coordinates before applying `(ETM21)`.

If all four versions of `(ETM19)` are present in the selected rank-five
packet **and their target translation images close on the same source-sized
paired orbits**, then:

```text
paired translations
 -> equivariant transition PVMs
 -> whole-map PVMs
 -> edgewise path classicalization
 -> common latent map law
 -> robust 1/36 contradiction.                      (ETM23)
```

The literal conjugation audit closes equivariance, but it does not by itself
prove the boldfaced same-orbit clause.  A proper translation embedding can
split matrix multiplicity into a larger target Weyl factor while preserving
total dimension and every equivariance relation.  The live input is a
carrier-coupled matrix-coordinate closure theorem ruling out that conversion.
No local computation or build was run for this note.
