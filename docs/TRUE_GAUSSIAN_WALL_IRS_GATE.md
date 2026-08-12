# The maximally-entangled character has an exact Gaussian wall model; IRS coherence is the missing discretization

Date: 2026-08-11

## Outcome

Every finite-dimensional unitary character occurring in the hyperlinear
problem has a canonical, dimension-free realization as the orbit length of
one set in a measured-wall action.  More precisely, after conjugate
tensoring, the deficit

```text
1-|tr_d(pi(g))|^2                                    (GWI1)
```

is half the square of a Hilbert displacement, and that Hilbert displacement
is exactly an `L^1` coboundary norm under Gaussian linearization.

Thus the unitary side already lies inside equivariant `L^1`/measured-wall
geometry.  The missing step is not an embedding of Hilbert distance into
`L^1`; that embedding is exact.  The missing step is to replace the resulting
arbitrary wall observable by a finite Schreier action whose **fixed-point**
length has the same normal `0/sqrt(2)` endpoint.  Equivalently, one must turn
wall cuts into subgroup/IRS membership cuts coherently.

This gives a new exact reformulation of the open problem and explains why
random partitions or cut decompositions alone do not prove TRUE.

## 1. Maximally-entangled displacement

Let `F` be a finitely generated free group and let

```text
pi:F -> U(d)                                           (GWI2)
```

be a representation.  On

```text
H_d=C^d tensor conjugate(C^d)                         (GWI3)
```

put

```text
rho_pi(g)=pi(g) tensor conjugate(pi(g)),
Omega_d=d^(-1/2) sum_i e_i tensor conjugate(e_i).     (GWI4)
```

Then

```text
<rho_pi(g)Omega_d,Omega_d>=|tr_d(pi(g))|^2.           (GWI5)
```

Hence

```text
ell_pi(g)
 :=||rho_pi(g)Omega_d-Omega_d||
 =sqrt(2-2|tr_d(pi(g))|^2).                           (GWI6)
```

This length is conjugation invariant.  It is also an orbit metric coming
from an honest orthogonal representation on the realification of `H_d`.

## 2. Equivariant Gaussian `L^1` linearization

Let `H_R` be a real Hilbert space.  On its standard Gaussian probability
space choose centered Gaussian variables `G_v`, linear in `v`, with

```text
E(G_v G_w)=<v,w>.                                    (GWI7)
```

The map

```text
J(v)=sqrt(pi/2) G_v                                  (GWI8)
```

is a real-linear isometry from `H_R` into `L^1`, because

```text
E|G_v|=sqrt(2/pi)||v||.                              (GWI9)
```

Every orthogonal operator `T` acts measure-preservingly on the Gaussian
space and satisfies

```text
J(Tv)=T dot J(v).                                    (GWI10)
```

Apply this to the realification of `(GWI4)` and set

```text
f_pi=J(Omega_d),
b_pi(g)=rho_pi(g) dot f_pi-f_pi.                     (GWI11)
```

Then `b_pi` is an exact `L^1` one-coboundary and

```text
||b_pi(g)||_1=ell_pi(g)
              =sqrt(2-2|tr_d(pi(g))|^2).             (GWI12)
```

There is no dependence on `d` in this conversion.

## 3. A one-set measured-wall realization

For a real integrable function `f` on a probability space `(Omega,mu)`, put

```text
A_f={(omega,t) in Omega x R : t<f(omega)}.           (GWI13)
```

The product measure is sigma-finite; the individual sets may have infinite
measure, but their symmetric differences have finite measure.  Layer-cake
integration gives

```text
(mu tensor dt)(A_f triangle A_h)=||f-h||_1.          (GWI14)
```

The Gaussian group action acts on the first coordinate.  Consequently

```text
(mu tensor dt)(A_(f_pi) triangle g A_(f_pi))
 =ell_pi(g).                                         (GWI15)
```

Thus every maximally-entangled coefficient deficit has an exact equivariant
measured-wall model using a single orbit of one set.

## 4. Normal-endpoint equivalence

Let `N normal F` and `Gamma=F/N`.  The normal-IRS character formulation in
the notepad yields the following equivalent statements.

**Theorem.**

1. `Gamma` is hyperlinear if and only if there are finite-dimensional
   representations `pi_n:F->U(d_n)` whose Gaussian lengths satisfy

   ```text
   ell_(pi_n)(g) -> 0        for g in N,
   ell_(pi_n)(g) -> sqrt(2)  for g notin N.           (GWI16)
   ```

2. `Gamma` is sofic if and only if there are finite actions
   `alpha_n:F action X_n` whose Hamming lengths satisfy

   ```text
   h_(alpha_n)(g)
    :=|{x:g x!=x}|/|X_n|
      ->0  for g in N,
      ->1  for g notin N.                            (GWI17)
   ```

**Proof.**  For (1), conjugate tensoring turns a finite-dimensional
character `chi_n` converging to `1_N` into `|chi_n|^2`; `(GWI6)` gives
`(GWI16)`.  Conversely `(GWI6)` recovers
`|chi_n(g)|^2->1_N(g)`.  The normalized character of the honest
`d_n^2`-dimensional representation
`rho_(pi_n)=pi_n tensor conjugate(pi_n)` is exactly `|chi_n|^2`.
Therefore the `rho_(pi_n)` themselves satisfy the usual finite-dimensional
character criterion for hyperlinearity.  This observation is important:
the Gaussian endpoint does not lose a scalar phase, because conjugate
tensoring turns its squared modulus back into the normalized trace of an
honest representation.

For (2),

```text
h_(alpha_n)(g)=1-|Fix(alpha_n(g))|/|X_n|.             (GWI18)
```

The finite-action character criterion gives the result.  End proof.

Therefore

```text
every hyperlinear group is sofic                            (GWI19)
```

is equivalent to the following special transfer principle:

> Every sequence of finite-dimensional Gaussian wall lengths with the
> normal endpoint `(GWI16)` can be replaced, on every growing finite word
> window, by finite Schreier Hamming lengths with endpoint `(GWI17)`.

This is narrower than approximating arbitrary measured-wall actions and
broader than pointwise rounding a unitary matrix.

## 5. The extra structure of finite-action lengths

If `x` is uniform in a finite `F`-set and `K_x=Stab_F(x)`, then

```text
1-h_alpha(g)=Prob[g in K_x].                         (GWI20)
```

The law of `K_x` is a finite-index IRS.  Thus a finite-action length is not
merely an invariant `L^1` length: its complement is a subgroup-membership
probability.  In particular it satisfies all implications forced by
subgroup closure, such as

```text
Fix(g) subset Fix(g^k),
h_alpha(g^k)<=h_alpha(g).                            (GWI21)
```

An arbitrary Gaussian wall length need not have this property.

For a concrete finite obstruction, let `p>=5` be prime, let
`F -> C_p=<zeta>` be the quotient, and take

```text
pi=1 direct-sum chi,
chi(zeta)=exp(2 pi i/p).                              (GWI22)
```

Then

```text
ell_pi(zeta^k)=sqrt(2)|sin(pi k/p)|.                 (GWI23)
```

This varies with nonzero `k`.  By contrast, in every finite `C_p`-action,
all nonidentity powers generate the same subgroup and hence have exactly
the same fixed-point set.  Therefore `(GWI23)` is not a finite-action
Hamming length and cannot even be uniformly approximated arbitrarily well
by such lengths on the whole finite group.

This does not contradict the target `(GWI16)`: `(GWI23)` is not a normal
`0/sqrt(2)` endpoint sequence.  It proves that the endpoint hypothesis is
essential and that generic `L^1` cut approximation is insufficient.

## 6. Why measured-wall sampling is not yet rounding

A cut decomposition samples sets so that symmetric-difference frequencies
approximate `(GWI15)`.  But a finite permutation model requires one coherent
action whose **point stabilizers** satisfy `(GWI20)`.  Sampling wall cuts
does not make those cuts cosets of subgroups and does not impose closure of
membership under products and powers.

Equivalently, quantizing the orbit of `A_(f_pi)` in the measure algebra must
identify nearby sets while respecting all tested products.  Treating every
distinct translate as a distinct atom loses the metric completely; an
arbitrarily small nonzero Gaussian displacement then moves every orbit
label.  Identifying nearby labels independently destroys multiplication.
This is the same table-dependent coherence obstruction already isolated by
the pointwise unitary-to-permutation no-go.

The precise remaining lemma is therefore a **normal-endpoint
subgroupification theorem**:

```text
Gaussian wall orbit lengths converging to 0 on N and sqrt(2) off N
   => finite-index IRS membership lengths converging to 0 on N and 1 off N.
                                                               (GWI24)
```

By `(GWI16)--(GWI20)`, `(GWI24)` is exactly the original open problem, not a
weaker corollary.  Its value is to remove a false analytic bottleneck:
Hilbert-to-`L^1` conversion and measured-wall realization are already exact;
all remaining difficulty is the arithmetic/combinatorial coherence that
turns arbitrary walls into stabilizers.
