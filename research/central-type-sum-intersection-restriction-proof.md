---
rg: 2
id: central-type-sum-intersection-restriction-proof
kind: route
title: Intersect group-basis supports and diagonalize the common finite subgroup
target: central-type-sum-equality-is-intersection-readable
requires: []
---

Put `C=H intersect K`. Distinct elements of `Gamma` are linearly
independent in `C[Gamma]`, so

```text
C[H] intersect C[K]=C[C].                               (CTS7)
```

Therefore every

```text
x in Z(C[H]) intersect Z(C[K])
```

belongs to `C[C]`. It commutes with `C`, hence belongs to `Z(C[C])`,
and has a unique expansion

```text
x=sum_(nu in Irr(C)) a_nu z_(C,nu).                    (CTS8)
```

Fix `rho in Irr(H)`. On the `nu`-isotypic summand of
`Res_C^H(rho)`, the operator `rho(x)` is scalar multiplication by
`a_nu`. Since `x` lies in `Z(C[H])`, Schur's lemma says that `rho(x)`
is scalar on the whole irreducible `H`-space. Thus

```text
a_nu=a_nu'
```

whenever `nu` and `nu'` co-occur in the restriction of one `H`-type.
The same argument for `K` shows that the coefficients in `(CTS8)` are
constant on every connected component of `R_C(H,K)`.

Conversely, suppose the coefficients are constant on those components. The
support of the restriction of any irreducible `H`-type is contained in one
component: every two of its constituents are joined by the defining
co-occurrence edge. Hence `(CTS8)` acts scalarly in every irreducible
representation of `H`, and so is central in `C[H]`. The same holds for
`K`. This proves `(CTS2)`.

The projections `e_Omega` are mutually orthogonal central projections.
Therefore an element of the right side of `(CTS2)` is a projection exactly
when its scalar coefficient on every component is `0` or `1`. This
proves that every common central projection is `e_U` for a union `U` of
components. On an irreducible `H`-space, `e_U` acts as `1` exactly when
the restriction support lies in `U`, and otherwise as `0`. Faithfulness
of the finite regular representation then gives

```text
e_U=sum_(rho: Supp Res_C^H(rho) subseteq U) z_(H,rho), (CTS9)
```

and the analogous formula for `K`. Equations `(CTS3)--(CTS4)` follow.
The canonical trace also records the exact Plancherel balance

```text
tau(e_U)=sum_(nu in U) dim(nu)^2/|C|
        =sum_(rho in S) dim(rho)^2/|H|
        =sum_(sigma in T) dim(sigma)^2/|K|.            (CTS10)
```

For the primitive-root consequence, let `q=z_(C,pi)` and let `P=e_U` be
a common central projection with `P<=q`. Since the primitive central
idempotents of `C[C]` are orthogonal,

```text
e_U q = q  if pi in U, and  e_U q=0 otherwise.
```

The order relation `P<=q` is the identity `Pq=P`. In the first case it
gives `P=q`; in the second it gives `P=0`. No assumption that `{pi}`
is already a component is needed. If it is not a union of components, the
`P=q` case is simply unavailable and zero is the only common subprojection.

For the Pauli specialization, `A,B,C` are abelian. Every irreducible type
is a character and restricts to a single character of `C`, so the
co-occurrence graph has singleton components. Every character of a subgroup
of a finite abelian group extends to the whole group, and Fourier
orthogonality gives

```text
z_(C,gamma)
 =sum_(alpha in Irr(A), alpha|_C=gamma) z_(A,alpha)
 =sum_(beta in Irr(B), beta|_C=gamma) z_(B,beta).       (CTS11)
```

Restricting `(CTS11)` to characters carrying the fixed central character
`zeta` proves `(CTS6)`. When `C=Z`, there is only one character of
`C` with that fixed value, so the marked common projection lattice is
`{0,q}`.

Finally, in an amalgamated free product, the normal-form theorem places the
intersection of finite subgroups carried by opposite vertex factors in the
amalgamated subgroup. The corresponding HNN assertion follows from Britton's
lemma: a base element represented by a one-stable-letter conjugate must come
from the associated subgroup. Applying `(CTS7)--(CTS11)` then makes every
chartwise-central equality a sum of edge-group types. This is covariance or
literal edge gluing, not additive multipath holonomy.
