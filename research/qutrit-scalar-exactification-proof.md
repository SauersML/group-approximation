---
rg: 2
id: qutrit-scalar-exactification-proof
kind: route
title: Exactify the finite scalar envelope and compute its qutrit weights
target: qutrit-scalar-exactification-has-no-central-index
requires:
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
  - weighted-unitary-hall-deficit-gap
---

Let `phi_l` be trace-preserving hyperlinear microstates on finite sets
which exhaust a group containing the finite subgroup

```text
K=GL_28(F_2).
```

After a diagonal extraction, all multiplication defects on `K` tend to
zero in normalized Hilbert--Schmidt norm.

Finite-group normalized-Hilbert--Schmidt stability applies here. One
self-contained route is to form the almost-intertwiner

```text
V_l xi=|K|^(-1/2) sum_(g in K) delta_g tensor phi_l(g)^* xi
```

from the microstate space to the tensor product of the left regular
`K`-space with that microstate space. Averaging its range projection over
the exact left regular action, then taking the polar part of the resulting
almost-intertwiner, produces an invariant subspace and an exact
representation. The discarded and added dimensions are `o(d_l)`, and the
polar intertwiner changes every named `K`-matrix by `o(1)` in normalized
Hilbert--Schmidt norm. Equivalently, this is the finite-group case of
normalized Frobenius stability for approximate unitary representations.

Denote the exact representation after this negligible stabilization by
`sigma_l:K->U(D_l)`, where `D_l/d_l->1`. Trace preservation and the
perturbation give

```text
tr_(D_l)(sigma_l(g)) -> 1  if g=1,
tr_(D_l)(sigma_l(g)) -> 0  if g!=1.                     (QSE2)
```

For an irreducible representation `pi` of `K`, character orthogonality
now computes its multiplicity `m_(pi,l)`:

```text
m_(pi,l)/D_l
 = (1/|K|) sum_(g in K)
       tr_(D_l)(sigma_l(g)) conjugate(chi_pi(g))
 -> dim(pi)/|K|.                                        (QSE3)
```

Thus the exact restrictions have the regular `K`-type proportions. If
`p` is any self-adjoint idempotent in `C[K]`, then
`sigma_l(p)` is a projection and `(QSE2)`, applied coefficientwise,
gives

```text
rank(sigma_l(p))/D_l -> tau_K(p),                        (QSE4)
```

where `tau_K` extracts the identity coefficient. The qutrit construction
has

```text
tau_K(q)=1/3,       tau_K(R)=2/9,       tau_K(q-R)=1/9.
```

Substitution in `(QSE4)` proves `(QSE1)`. Replacing `D_l` by the
original dimension changes none of the limits.

If `U_l` is any unitary, then

```text
rank(U_l sigma_l(p) U_l^*)=rank(sigma_l(p)).
```

Hence actor conjugacy by itself cannot change any source or target weight.
A Hall obstruction would require an additional relation which kills named
blocks or forces their range into a strictly smaller sum of target
projections.

It remains to exclude the tempting central route. Since the field has two
elements,

```text
GL_28(F_2)=SL_28(F_2)=PSL_28(F_2).
```

This group is perfect. The standard Schur-multiplier formula for
`PSL_n(q)` gives multiplier of order `gcd(n,q-1)` outside the familiar
small exceptional pairs; `(n,q)=(28,2)` is not exceptional and the order
is `gcd(28,1)=1`. Therefore

```text
H_1(K,Z)=0,                  H_2(K,Z)=0.                 (QSE5)
```

For a trivial `K`-module `A`, the universal-coefficient sequence and
`(QSE5)` give `H^2(K,A)=0`. Every central extension of `K` by the
abelian group `A` therefore splits. Its splittings form a torsor for
`Hom(K,A)`, which is also zero because `K` is perfect, so the splitting
is unique. In particular, a central involution only gives `K x C_2`.

This computation does not address a noncentral head cut. In a canonical
microstate a nonidentity head involution has trace tending to zero, so its
negative spectral cut has asymptotic weight one half; that case requires
joint exactification of the larger finite head envelope and is treated
separately. The present result closes only bare conjugacy and central-phase
arguments.
