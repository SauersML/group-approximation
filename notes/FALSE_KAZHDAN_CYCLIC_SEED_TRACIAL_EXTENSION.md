# The cyclic-seed Kazhdan estimate is intrinsically tracial

Date: 2026-08-12

## 1. Outcome

The matrix estimate in
`FALSE_KAZHDAN_CYCLIC_SEED_PROPAGATION_NO_GO.md` does not use finite
dimensionality.  It holds in the standard Hilbert space of every finite
tracial von Neumann algebra, with the same Kazhdan constant and the same
orbit-coefficient cost.

Let `Gamma=<S>` have property `(T)`, with

```text
dist(xi,Fix_Gamma pi)
 <=kappa^(-1) max_(s in S)||pi(s)xi-xi||             (KST1)
```

for every unitary representation `pi`.  Let `W` be an additive
`Gamma`-module.  Let `(M,tau)` be a finite tracial von Neumann algebra, and
suppose

```text
rho_i:Gamma->U(M),       Phi_i:W->U(M),       i=0,1, (KST2)
```

are homomorphisms satisfying exact covariance

```text
rho_i(g)Phi_i(w)rho_i(g)^*=Phi_i(gw).                 (KST3)
```

For `z,w in W`, put

```text
c_Gamma(w;z)=min sum_nu |n_nu|,                      (KST4)
```

where the minimum runs over all finite expressions

```text
w=sum_nu n_nu g_nu z,
n_nu in Z, g_nu in Gamma,                            (KST5)
```

and set the value to infinity when no such expression exists.

**Theorem 1 (tracial cyclic-seed propagation).**  Let `T in L^2(M,tau)`
and suppose `C=c_Gamma(w;z)<infinity`.  Define

```text
epsilon=||Phi_0(z)T-T Phi_1(z)||_2,
eta=max_(s in S)||rho_0(s)T-T rho_1(s)||_2.           (KST6)
```

Then

```text
||Phi_0(w)T-T Phi_1(w)||_2
 <=C epsilon+2(C+1)eta/kappa.                        (KST7)
```

No boundedness or unitarity assumption on the comparison vector `T` is
needed.  In particular, `(KST7)` applies simultaneously to matrix
microstates, finite factors, Connes-embeddable tracial algebras, and
commuting-operator tracial models whenever the base and tangent covariance
are exact.

For the paired Frobenius labels in the preceding note, the explicit
four-orbit formula gives `C<=2r`.  Hence

```text
||Phi_0(z_-)T-T Phi_1(z_-)||_2
 <=2r epsilon+(4r+2)eta/kappa.                       (KST8)
```

Thus the exact-covariance no-go is not a finite-dimensional compactness
artifact.  Escaping it requires genuinely approximate/nonliftable
covariance, not merely passing to an infinite tracial target.

## 2. Kazhdan projection in the standard form

On `L^2(M,tau)` define

```text
beta(g)xi=rho_0(g) xi rho_1(g)^*.                    (KST9)
```

Left and right multiplication by unitaries preserve the tracial
`L^2`-norm, and the two actions commute.  Therefore `beta` is a unitary
representation of `Gamma`.  Let `P` be the orthogonal projection onto its
invariant vectors and put

```text
X=PT,        delta=||T-X||_2.                        (KST10)
```

Property `(T)` gives

```text
delta<=eta/kappa.                                    (KST11)
```

The invariant-vector identity is

```text
rho_0(g)X=X rho_1(g),       g in Gamma.              (KST12)
```

This statement is meaningful for `X in L^2(M,tau)`: multiplication on
either side by an element of `M` is a bounded operator on `L^2(M,tau)`.
The seed discrepancy after projection obeys

```text
||Phi_0(z)X-X Phi_1(z)||_2<=epsilon+2delta.           (KST13)
```

## 3. Exact transport and additive propagation

Equations `(KST3)` and `(KST12)` give, for every `g in Gamma`,

```text
Phi_0(gz)X-X Phi_1(gz)
 =rho_0(g)(Phi_0(z)X-X Phi_1(z))rho_1(g)^*.           (KST14)
```

Consequently

```text
||Phi_0(gz)X-X Phi_1(gz)||_2<=epsilon+2delta         (KST15)
```

uniformly over the whole group; no word length occurs.

For unitaries `U,V in M`, `Y in L^2(M,tau)`, and `n in Z`, telescoping
gives

```text
||U^nY-YV^n||_2<=|n| ||UY-YV||_2.                   (KST16)
```

The analogous product inequality is

```text
||U_1...U_mY-YV_1...V_m||_2
 <=sum_j ||U_jY-YV_j||_2.                            (KST17)
```

Apply these inequalities to a coefficient-minimizing expression `(KST5)`.
Since each `Phi_i` is a homomorphism of the additive group,

```text
||Phi_0(w)X-X Phi_1(w)||_2
 <=C(epsilon+2delta).                                (KST18)
```

Replacing `X` by `T` costs at most `2delta`.  Combining `(KST11)` and
`(KST18)` proves `(KST7)`.

## 4. Ultraproduct consequence

Let `(M_n,tau_n)` be arbitrary finite tracial von Neumann algebras and let
`(rho_(i,n),Phi_(i,n))` satisfy exact covariance.  Suppose `T_n` are
uniformly `L^2`-bounded and

```text
epsilon_n->0,       eta_n->0.                        (KST19)
```

For every sequence `w_n` admitting expressions from `z_n` with one uniform
bound

```text
sup_n c_Gamma(w_n;z_n)<infinity,                     (KST20)
```

Theorem 1 gives

```text
||Phi_(0,n)(w_n)T_n-T_n Phi_(1,n)(w_n)||_2->0.       (KST21)
```

Equivalently, in any tracial ultraproduct the exact base-intertwiner
obtained from the Kazhdan projection transports one aligned cyclic seed to
its entire bounded orbit-coefficient span.  This is stronger than a
finite-dimensional subsequence argument and requires neither matrix
rounding nor Connes embeddability.

## 5. Scope

The exactness of `(KST2)--(KST3)` is load-bearing.  Projecting `T` produces
an exact base intertwiner, but it does not repair an approximately
covariant tangent character field.  In the current FALSE program that
remaining field is deliberately required to be uniformly far from every
exact covariant realization.  The theorem therefore closes the following
possible escape and no more:

> increasing the target from matrices to arbitrary finite tracial algebras
> cannot preserve the inverse fold if the two base actions and their
> tangent covariance are exact.

The live construction must still produce a genuinely nonliftable
normalized-`L^2` covariance system.  That is the same boundary identified
finitely in `FALSE_EQUIVARIANT_FIBER_FUNCTOR_STABILIZER_REDUCTION.md`, now
shown to remain the boundary in every finite tracial target.
