---
rg: 2
id: sofic-chart-fourier-energy-floor-proof
kind: route
title: Fourier-linearize each local action chart and apply the seed-visible Schreier gap
target: sofic-chart-quotient-forces-character-energy-floor
requires:
  - gkp-sofic-action-is-liftable-hamming-chart-family
  - infinite-schreier-pvm-transport-kills-finite-mark
  - whole-module-covariance-average-equals-character-transport
  - sofic-action-gives-marked-pauli-central-product-microstates
artifacts:
  - research/artifacts/sofic-chart-character-energy-floor-2026-08-30.md
---

Fix a finite word window and enlarge its finite site set `E` to contain the
support of `m_0`, every module support occurring in the window, and every
actor translate needed to evaluate the window.  Soficity of the action gives
finite carriers `D_n`, almost-multiplicative permutations `sigma_(s,n)`, and
labels

```text
ell_(x,n):D_n->N_n,       x in E,
```

such that, outside a set of density `o(1)`,

```text
ell_(sx,n)(sigma_(s,n)d)=ell_(x,n)(d)                    (SCF1)
```

for every required `(s,x)`, and `x |-> ell_(x,n)(d)` is injective on `E`.
The finite label range may be taken as `N_n`; extend the labels arbitrarily
to `x outside E`.

Put `B_n=F_2^(N_n)` and

```text
H_n=ell^2(D_n x B_n).
```

For `d in D_n` define the linear map

```text
j_(n,d)(m)=sum_x m_x delta_(ell_(x,n)(d)) in F_2^(N_n)
```

and set

```text
rho_n(m)e_(d,b)=(-1)^(<b,j_(n,d)(m)>) e_(d,b).           (SCF2)
```

Linearity of every `j_(n,d)` makes `rho_n` an exact representation of the
whole infinite module `M`, independent of label collisions.  Let

```text
C_s^(n)e_(d,b)=e_(sigma_(s,n)d,b).
```

Equation `(SCF1)` gives exact covariance on every good chart carrier.
Therefore covariance for each fixed module word has defect `o(1)`, and
almost multiplicativity of `sigma_n` gives defect `o(1)` for every actor
relation in the fixed window.  Telescoping handles every mixed word in that
window.

On a carrier where the labels are injective on `supp(m_0)`, the vector
`j_(n,d)(m_0)` is nonzero.  Exactly half of the uniformly distributed
`b in B_n` then satisfy

```text
<b,j_(n,d)(m_0)>=1.
```

The good-carrier density tends to one, proving `(SCQ1)`.

Let `(P_chi^(n))` be the finite spectral PVM of `rho_n`.  Take `Omega_n` to
be the union of the `A`-orbits of all occurring characters with
`chi(m_0)=-1`.  It is a finite union of countable orbits, and the direct-sum
Schreier operator on `Omega_n` has bottom gap at least `gamma`.  Moreover,

```text
sum_(chi in Omega_n) tr(P_chi^(n)) >= 1/2-o(1).
```

Apply `infinite-schreier-pvm-transport-kills-finite-mark` to the projections
indexed by `Omega_n`, putting zero on the orbit points absent from the finite
spectrum.  Since `Omega_n` is invariant, its energy is a sub-sum of the full
energy, and hence

```text
E_n >= 2 gamma (1/2-o(1))=gamma-o(1).
```

The whole-module averaging identity now gives `(SCQ3)`.

For robustness, let `Q_n^-=(1-rho'_n(m_0))/2`.  Since both seed operators
are selfadjoint involutions,

```text
|tr(Q_n^-)-tr((1-rho_n(m_0))/2)|
 <= (1/2)||rho'_n(m_0)-rho_n(m_0)||_2.                  (SCF3)
```

Thus the seed-negative mass of `rho'_n` is again `1/2-o(1)`.  Repeating the
Schreier-gap estimate on the orbits of its occurring seed-negative
characters proves the same energy floor.  This rules out every decoder
which preserves the named seed.

Finally, the replicated-center Pauli chart uses the same pushed-forward
first lamp coordinate.  Restricting its fibrewise left-regular
representation to that coordinate is a multiple of `(SCF2)`.  Hence the
same energy floor holds while the additional Pauli operators satisfy the
bare seed relations and the common mark remains separated.  Any controller
which escapes the theorem must therefore destroy that quotient.