---
rg: 2
id: cartan-collision-rounding-proof
kind: route
title: Match localized columns and discard their diagonal phases
target: collision-and-phase-free-cartan-observables-force-joint-lamp-targets
requires:
  - finite-lamp-targets-glue-after-action-groupoid-completion
  - finite-schreier-holonomy-is-the-lamp-gauge-obstruction
---

## Step 1: collision mass gives a large injective column matching

For column `j`, put

```text
p_(ij)=|u_ij|^2,       m_j=max_i p_(ij),       sum_i p_(ij)=1.
```

Since `sum_i p_(ij)^2<=m_j`,

```text
d^(-1)sum_j m_j >= Col_D(U)>=1-eta.                     (CPR1)
```

Thus the average deficit `1-m_j` is at most `eta`.  Markov's inequality
shows that the good set

```text
J={j:m_j>=1-sqrt(eta)}
```

has size at least `(1-sqrt(eta))d`.  Because
`1-sqrt(eta)>1/2`, two good columns cannot have their maximum in the same
row: the squared moduli in that row would sum to more than one.  The
maximizing-row map is therefore injective on `J`.

Extend it arbitrarily to a permutation `pi` of all rows and columns.  Put
a phase of modulus one at `(pi(j),j)`, choosing the phase of
`u_(pi(j),j)` whenever that entry is nonzero.  The resulting matrix `M`
is monomial and

```text
Re tau(M^*U)
 =d^(-1)sum_j |u_(pi(j),j)|
 >=(1-sqrt(eta))sqrt(1-sqrt(eta))
 =(1-sqrt(eta))^(3/2).                                  (CPR2)
```

For `0<=x<=1`, `(1-x)^(3/2)>=1-(3/2)x`.  Hence

```text
||U-M||_2^2
 =2-2 Re tau(M^*U)
 <=2-2(1-sqrt(eta))^(3/2)
 <=3sqrt(eta).                                          (CPR3)
```

This proves `(CPC3)`.  Write `M=A sigma` with `A` diagonal unitary and
`sigma` a permutation matrix.  Conjugation by `M` and by `sigma`
agree on `D_d`, so all diagonal phases may be discarded for the action on
cylinder projections.

## Step 2: actor multiplication survives phase removal

Choose monomial approximants `M_g,M_h,M_k` by Step 1.  Unitary invariance
and the triangle inequality give

```text
||M_g M_h-M_k||_2
 <=||M_g-U_g||_2+||M_h-U_h||_2
   +||U_g U_h-U_k||_2+||U_k-M_k||_2
 <=a_g+a_h+delta_(g,h,k)+a_k.                           (CPR4)
```

If the permutation parts of `M_gM_h` and `M_k` differ on a fraction
`q` of the columns, then on every such column the two monomial images are
supported on distinct basis vectors.  The squared Euclidean difference on
that column is exactly two, irrespective of phase.  Therefore

```text
||M_gM_h-M_k||_2^2>=2q.                                 (CPR5)
```

Combining `(CPR4)--(CPR5)` proves `(CPC4)`.

## Step 3: cylinder covariance becomes Hamming covariance

Let `P,Q` be diagonal projections and suppose

```text
||U P U^*-Q||_2<=epsilon,       ||U-M||_2<=a.
```

Then

```text
||M P M^*-Q||_2
 <=epsilon+||M P M^*-U P U^*||_2
 <=epsilon+2a.                                          (CPR6)
```

The two projections in `(CPR6)` are diagonal, and `Ad(M)|D=Ad(sigma)|D`.
Their squared normalized Hilbert--Schmidt distance is exactly the normalized
cardinality of the symmetric difference of their supports.  Squaring
`(CPR6)` proves `(CPC5)`.

This estimate can be imposed simultaneously on every character projection
in a fixed union window.  The union/refinement estimate in
`moving-lamp-refinement-cocycle-has-diffuse-fibers` supplies the preceding
covariance error from coordinate-lamp errors; no independently chosen
overlap coupling is used.

## Step 4: phase-free mass is exactly permutation fixed mass

For a monomial `M=A sigma`, its diagonal conditional expectation retains
one modulus-one entry exactly at each fixed point of `sigma`.  Hence

```text
||E_D(M)||_2^2=FixFrac(sigma).                           (CPR7)
```

Conditional expectation is contractive in normalized Hilbert--Schmidt norm,
so

```text
sqrt(FixFrac(sigma))
 =||E_D(M)||_2
 <=||E_D(U)||_2+||M-U||_2
 <=sqrt(Fix_D(U))+a.                                    (CPR8)
```

Squaring proves `(CPC6)`.

The use of `Fix_D`, rather than `|tau(U)|`, is essential.  A diagonal
unitary may have cancelling phases and scalar trace zero while its
underlying permutation is the identity.  Formula `(CPR7)` removes that
cancellation.

## Step 5: why a uniform Boolean Ulam theorem is the target itself

Let `G` act p.m.p. on `(X,mu)`, and suppose
`L^infinity(X) crossed_product G` is Connes embeddable.  For every finite
family of measurable sets, actor words, products, and covariance relations,
Connes embeddability supplies matrix microstates matching that finite
crossed-product table and its traces.

Assume a uniform extraction theorem produced, for these microstates and
along an exhaustion, rank-one masas `D_d` such that

1. the chosen finite Boolean projections lie in `D_d`, up to vanishing
   Hilbert--Schmidt error;
2. `Col_D(U_w)->1` for every tested actor word;
3. `Fix_D(U_w)->0` for every nonidentity actor word.

Steps 1--4 turn each sufficiently accurate table into a finite diagonal
Boolean model and approximately multiplicative permutation actor maps.
Equation `(CPC5)` gives covariance, `(CPC4)` gives actor multiplication,
and `(CPC6)` gives the faithful sofic trace.  A diagonal choice over the
finite tables gives an embedding with the function algebra diagonal and the
actor unitaries permutation-valued.  This is exactly Păunescu's definition
of a sofic p.m.p. action.

In the other direction, a sofic action already has such coordinate models.
Take their diagonal masas and permutation actor matrices.  Then
`Col_D(U)=1` exactly, and `Fix_D(U_w)` is the fixed-point fraction, which
tends to zero for nonidentity words.

Thus the existence of these observables across every growing Boolean window
is an equivalent spatial form of the desired action model.  Finite
dimensionality alone only proves stability after a finite action groupoid is
already fixed; that positive case is
`finite-lamp-targets-glue-after-action-groupoid-completion`.  It gives no
uniform procedure for choosing the common masas in an arbitrary
crossed-product microstate.  For the Kun--Thom Bernoulli action, such a
procedure would contradict its established nonsoficity and therefore prove
the crossed product non-CE.  That is the intended global theorem, not an
available Ulam lemma.
