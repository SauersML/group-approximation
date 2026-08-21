---
rg: 2
id: finite-game-gap-makes-the-cyclic-acceptance-compressor-strict
kind: claim
title: A finite game gap makes the cyclic product of all acceptance projections a strict contraction
distinct_from:
  one-product-of-verifier-reflections-does-not-control-game-energy: that shows phase cancellation for a unitary product of reflections; this replaces the reflections by positive acceptance compressions and proves the missing contraction.
  one-gram-vector-decodes-a-finite-bcs-strategy: that lower-bounds the sum of all rejection energies on a supplied Gram operator; this packages the same gap into one sequential return operator and no longer assumes the supplied operator has low energy.
  fanizza-heat-filter-has-uniform-cstar-decay: that uses an infinite functional-calculus family; this uses one finite product of the fixed game's local acceptance projections.
---

Let `K` be a finite-dimensional Hilbert space and let

```text
L_1,...,L_m                                             (CAP1)
```

be orthogonal projections.  Think of `L_j` as the rejected-event
projections of one fixed finite game.  Let `alpha_j>0` and suppose

```text
sum_j alpha_j ||L_j xi||^2 >=lambda||xi||^2            (CAP2)
```

for every `xi in K`, where `lambda>0`.  Put

```text
Q_j=I-L_j,
T=Q_m Q_(m-1)...Q_1,
C=alpha_max m(m+1)/2.                                  (CAP3)
```

Then

```text
||T||_op^2<=1-lambda/C,                                (CAP4)
```

and hence, with

```text
kappa=1-sqrt(1-lambda/C)>0,
```

```text
||(T-I)xi||>=kappa||xi||                               (CAP5)
```

for every `xi`.

## Proof

Set

```text
xi_0=xi,
xi_j=Q_j xi_(j-1),
d_j=L_j xi_(j-1).                                      (CAP6)
```

Orthogonality gives the exact telescoping identity

```text
||xi||^2-||Txi||^2=sum_j||d_j||^2.                    (CAP7)
```

Moreover

```text
||L_jxi||
 <=||xi-xi_(j-1)||+||d_j||
 <=sum_(i<=j)||d_i||.                                  (CAP8)
```

By Cauchy--Schwarz,

```text
sum_j alpha_j||L_jxi||^2
 <=alpha_max sum_j j sum_(i<=j)||d_i||^2
 <=C sum_i||d_i||^2.                                  (CAP9)
```

Combine `(CAP2)`, `(CAP7)`, and `(CAP9)` to get `(CAP4)`.
The reverse triangle inequality then gives `(CAP5)`.  All constants depend
only on the fixed list of tests and not on `dim K`.

## The BCS Gram-space specialization

Fix context PVMs and Bob involutions as in
`one-gram-vector-decodes-a-finite-bcs-strategy`, and work on the Hilbert
space

```text
K_d=L^2(M_d(C),tr_d).                                   (CAP10)
```

Every term of the BCS Gram energy is the squared norm of an orthogonal
rejection projection:

```text
predicate rejection:
  L_c^pred(G)=F_cG,

consistency rejection:
  L_(c,x)^cons(G)=(G-A_(c,x)G B_x)/2.                  (CAP11)
```

The second map is a projection because

```text
G -> A_(c,x)G B_x                                      (CAP12)
```

is a self-adjoint unitary on `(CAP10)`.  Moreover

```text
||L_(c,x)^cons(G)||_2^2
 =||A_(c,x)G-GB_x||_2^2/4.                            (CAP13)
```

If the finite-dimensional value of the fixed game is at most `theta<1`,
the Gram-Rayleigh theorem gives `(CAP2)` with

```text
lambda=1-theta                                        (CAP14)
```

and the rational question weights as the `alpha_j` (duplicated between the
predicate and consistency rows as necessary).  Therefore the fixed cyclic
acceptance compressor

```text
T_game=product_j (I-L_j)                               (CAP15)
```

satisfies one dimension-free strict-contraction estimate on **every** finite
matrix realization of the measurement tables.

In an exact perfect commuting strategy, by contrast, the perfect strategy
vector lies in the kernel of every `L_j`; hence it is a nonzero fixed vector
of `(CAP15)`.  The finite/infinite asymmetry is exactly the one needed for a
groupification cell.

## Finite Hecke expansion

Every factor in `(CAP15)` is an explicit finite left-right operator:

```text
Q_c^pred(G)=(I-F_c)G,

Q_(c,x)^cons(G)=(G+A_(c,x)G B_x)/2.                   (CAP16)
```

Consequently their fixed finite product has an expansion

```text
T_game(G)=sum_(s=1)^N beta_s U_s G V_s,               (CAP17)
```

where `N`, the rational coefficients `beta_s`, and the left/right words
`U_s,V_s` depend only on the one fixed game.  Thus the full positive verifier
has been compressed into one finite Hecke bimodule coefficient; there is no
runtime or dimension dependence.

The matrix-only endpoint can now be stated with one Gram block:

```text
||G||_2^2>=gamma q-o(1),
||T_game(G)-G||_2^2<=K E_rel+o(1).                    (CAP18)
```

Equations `(CAP5)` and `(CAP18)` immediately give

```text
kappa^2 gamma q<=K E_rel+o(1).                         (CAP19)
```

This is equivalent in strength to the predicate/anchor part of `(FPG19)`,
but it does not first require proving that `G` has low energy under every
test.  Approximate cyclic return forces that conclusion through the game
gap.

## Exact status of the new route

The analytic contraction `(CAP4)` and finite expansion `(CAP17)` are
complete.  The unresolved group-word theorem is to construct one marked
positive-norm `G` and make the finite Hecke sum `(CAP17)` return it with the
estimate `(CAP18)`.  A coefficient-ring/Steinberg linearization can name the
finite sum, but the usual same-reservoir/root-to-coefficient normalized-HS
interface is still required.  Thus this result does not claim the final
non-hyperlinear group.

It does improve the target: instead of authenticating every context
predicate and anchor covariance row separately, authenticate one finite
cyclic acceptance return.  Unlike a product of reflections, the return has
an a priori dimension-free spectral gap and cannot disappear by phase
cancellation.

`cyclic-acceptance-root-needs-kernel-reflection`
performs the exact ordinary coefficient/Steinberg packaging.  After one
fixed denominator clearing, `D(T_game(G)-G)` is already a single coefficient
and one root names it.  The product positivity supplies the lower bound
`(CAP19)`, but the D8 decoupling model shows that it does not supply the
root-to-coefficient upper bound: the remaining interface is still the
one-coordinate kernel-reflection property `(CRB8)`.

`block-encoded-acceptance-still-needs-corner-return` gives a complementary
unitary packaging.  With one fresh control qubit per test, the all-zero
corner of one fixed ordinary unitary is exactly `T_game`.  This avoids the
additive Steinberg sum, but leaves one source-saturation scalar and one mixed
corner-return scalar; finite wreath naming does not authenticate either
against the analytic marked source.
