---
rg: 2
id: high-density-local-sectors-force-one-bcs-gram
kind: claim
title: High-density local predicate sectors force one common finite BCS Gram carrier
distinct_from:
  finite-product-selected-type-mark-does-not-align-carriers: that shows positive product norm and pairwise overlap do not imply a nonzero meet; this assumes an actual family of projections whose total codimension is small enough to force a meet, and quantifies the BCS error it must carry.
  tensor-context-types-classicalize-common-source: that obtains an exact classical contradiction by making all context algebras commute on a tensor-product source; this does not assume cross-context commutation and instead decodes a generally entangled finite strategy from the meet.
  summable-reducing-carriers-force-infinite-clifford-capacity: that assumes every carrier reduces the Clifford observables; here no local carrier is reducing, and small total codimension alone controls the commutator of their meet with every bounded observable.
  one-gram-vector-decodes-a-finite-bcs-strategy: that proves the game gap once one Gram operator is already available; this manufactures that Gram operator as a meet and gives an explicit density threshold in terms of local predicate-sector masses.
---

ESTABLISHED.
Let `B` be a finite constraint-variable BCS game with finite-dimensional
value at most `theta<1`.  Use the notation of
`one-gram-vector-decodes-a-finite-bcs-strategy`: context PVMs
`P_(c,a)`, forbidden projections `F_c`, context involutions `A_(c,x)`,
Bob involutions `B_x`, and rational question distribution `mu_(c,x)`.
Put

```text
Delta=1-theta,                 mu_c=sum_(x in c)mu_(c,x).             (HD1)
```

For arbitrary projections `q_c in M_d(C)`, define

```text
p=meet_(c) q_c,
eta=sum_c tr(1-q_c),
epsilon_c=||F_c q_c||_2,
kappa_(c,x)=||(A_(c,x)-B_x)q_c||_2.                                  (HD2)
```

Then

```text
tr(p)>=1-eta                                                         (HD3)
```

and the following dimension-independent inequality holds:

```text
Delta(1-eta)
 <= sum_c mu_c epsilon_c^2
    +(1/2)sum_(c,x)mu_(c,x)kappa_(c,x)^2
    +eta.                                                            (HD4)
```

In particular, if every local predicate and occurrence-consistency row is
exact on its own sector, then

```text
eta >= Delta/(1+Delta).                                              (HD5)
```

Thus a family of exact local predicate sectors whose total missing density
is below `Delta/(1+Delta)` cannot occur in any finite-dimensional model.
This is a genuine analytic-intersection criterion: the `q_c` need not
commute with one another, with the context observables, or with the Bob
observables.

## Proof

The elementary codimension inequality for subspaces gives

```text
dim(intersection_c ran(q_c))
 >= d-sum_c codim(ran(q_c)),                                         (HD6)
```

which is `(HD3)`.  Equivalently,

```text
tr(1-p)<=eta.                                                        (HD7)
```

For every self-adjoint unitary `B`, the two off-diagonal corners in

```text
[B,p]=(1-p)Bp-pB(1-p)                                                (HD8)
```

are Hilbert--Schmidt orthogonal.  Each has squared normalized
Hilbert--Schmidt norm at most `tr(1-p)`.  Hence

```text
||[B,p]||_2^2<=2tr(1-p)<=2eta.                                       (HD9)
```

Because `p=q_cp`, right compression by `p` gives

```text
||F_cp||_2<=epsilon_c,
||(A_(c,x)-B_x)p||_2<=kappa_(c,x).                                  (HD10)
```

Use `G=p` in the one-Gram energy.  Its consistency row satisfies

```text
A_(c,x)p-pB_x
 =(A_(c,x)-B_x)p+[B_x,p],                                           (HD11)
```

and therefore, by `(HD9)` and `||u+v||_2^2<=2||u||_2^2+2||v||_2^2`,

```text
(1/4)||A_(c,x)p-pB_x||_2^2
 <=(1/2)kappa_(c,x)^2+eta.                                          (HD12)
```

Summing with `mu`, whose total mass is one, shows

```text
E_p
 <=sum_c mu_c epsilon_c^2
   +(1/2)sum_(c,x)mu_(c,x)kappa_(c,x)^2+eta.                         (HD13)
```

The one-Gram gap gives `E_p>=Delta||p||_2^2=Delta tr(p)`.  Combine
this with `(HD3)` and `(HD13)` to obtain `(HD4)`.  Setting the local
errors to zero and rearranging gives `(HD5)`.

## Canonical Plancherel corollary

Suppose a proposed groupifier places `q_c` in finite subgroup algebras and
canonical microstates exactify those subgroups.  If their canonical
Plancherel masses are

```text
alpha_c=tau_Gamma(q_c),
eta_0=sum_c(1-alpha_c),                                              (HD14)
```

then the microstates have `eta=eta_0+o(1)`.  If the presentation also makes
the local predicate and occurrence-consistency errors `o(1)`, `(HD4)`
excludes canonical microstates whenever

```text
eta_0<Delta/(1+Delta).                                               (HD15)
```

Consequently `(HD15)` is a sufficient quantitative soundness target for a
high-density signed-Hecke or finite-subgroup atlas.  It avoids the false
inference from a surviving noncommutative product to a common carrier: the
carrier here is forced by total codimension.

It also identifies the sharp immediate gate for the usual selected-type
packets.  Their masses are fixed by Plancherel theory.  If their total
deficit is at least `Delta/(1+Delta)`, the density argument alone supplies
no contradiction; one must amplify the selected masses or use a different
common-Gram mechanism.  Conversely, any atlas crossing `(HD15)` only needs
ordinary group-word control of the finitely many local rows in `(HD2)`.

The argument is deliberately matrix-only.  A perfect commuting strategy
may exist in an infinite tracial algebra even though the finite game has
gap `Delta`; thus this criterion does not incorrectly reject the intended
non-Connes-embeddable exact witness.

There is a separate, strictly rowwise alternative when no useful meet can be
authenticated.  `independent-row-masks-transfer-bcs-gap-to-ambient-identity`
tests the same global context PVMs and Bob involutions against `G=I`, allows a
different projection for every predicate and consistency row, and pays their
weighted codimensions directly.  Exact rows are then impossible as soon as
that weighted deficit is below `Delta`.  This does not improve `(HD5)` for a
known common meet; it bypasses the meet construction altogether.
