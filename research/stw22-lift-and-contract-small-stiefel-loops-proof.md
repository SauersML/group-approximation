---
rg: 2
id: stw22-lift-and-contract-small-stiefel-loops-proof
kind: route
title: Lift small frame loops near the identity and contract them through the hyperfinite corner
target: stw22-strong-stiefel-spaces-have-uniform-loop-fillings
requires: []
artifacts:
  - research/artifacts/stw22-uniform-stiefel-loop-filling-audit-2026-08-30.md
---

Fix `p,e,v_0` as in the claim and put `q_0=v_0v_0^*`.  The case `p=0`
is trivial.  All `2`-norms below are computed using the ambient trace.

## A quantitative pointwise unitary extension

Let `v in V(p,e)` and suppose `||v-v_0||_2<delta`.  Put `q=vv^*`.  Then

```text
||q-q_0||_2<=2 delta.                                  (UL1)
```

The standard two-projection perturbation lemma in a finite von Neumann
algebra gives `u_1 in U(eRe)` such that

```text
u_1q_0u_1^*=q,
||u_1-e||_2<=2 sqrt(2)||q-q_0||_2<=4 sqrt(2)delta.       (UL2)
```

This is Takesaki, *Theory of Operator Algebras III*, Lemma XIV.2.1; the
same quantitative form is recorded in Farah--Vaccaro, Claim 3.1.

Both `u_1v_0` and `v` have initial projection `p` and final projection
`q`.  Hence

```text
c=v^*u_1v_0 in U(pRp).
```

Set

```text
u_2=v_0c^*v_0^*+(e-q_0),       u=u_1u_2.
```

Then `uv_0=v`, and

```text
||u_2-e||_2=||c-p||_2
 <=||u_1v_0-v||_2
 <=||u_1-e||_2+delta,

||u-e||_2<13 delta.                                    (UL3)
```

Only the existence and the uniform estimate in `(UL3)` are used; this
pointwise choice need not vary continuously.

## The conjugator fibres form one uniformly equi-`LC^0` family

Regard `L^2(R)` as a real Hilbert space.  For all choices of `e,p,v_0,v`
as above, consider the closed subset

```text
G(e,p;v_0,v)={u in U(eRe):uv_0=v} subset L^2(R).        (UL4)
```

These sets are nonempty by `(UL3)`.  They are `2`-norm closed.  Indeed, a
`2`-norm limit of unitaries in one corner is still in that corner and is
unitary: uniform operator-norm boundedness puts the limit in `eRe`, while
`2`-norm convergence and

```text
||x_n^*x_n-x^*x||_1
 <= (||x_n||_2+||x||_2)||x_n-x||_2
```

preserve both unitary equations.  Multiplication by the fixed `v_0` is
`2`-norm continuous, so the conjugator equation is also preserved.

The family of all sets `(UL4)`, with every admissible choice of the four
parameters, is uniformly equi-`LC^0` in the common Hilbert space `L^2(R)`.
To see this, take `u_0,u_1` in one fibre and put `h=u_0^*u_1`.  Then
`hv_0=v_0`, so the principal-logarithm path

```text
u_t=u_0 exp(t log(h)),       0<=t<=1,                  (UL5)
```

stays in the same fibre.  Scalar functional calculus on the principal
branch gives

```text
||u_t-u_0||_2<=||u_1-u_0||_2.                          (UL6)
```

Consequently the image of `(UL5)` has diameter at most
`2||u_1-u_0||_2`.  Thus `delta_0(eta)=eta/2` is a single uniform
`LC^0` modulus for the whole family, independent of all corner traces.

## A controlled Michael selection gives the loop lift

For the given loop define

```text
Phi(z)=G(e,p;v_0,v(z)),       z in S^1.                (UL7)
```

This multifunction is lower semicontinuous, without invoking any local
orbit section.  Indeed, if `v_n->v`, `u in G(e,p;v_0,v)`, apply the
pointwise construction `(UL1)--(UL3)` to the two frames `v` and `v_n`.
It gives `a_n in U(eRe)` such that

```text
a_nv=v_n,       ||a_n-e||_2<13||v_n-v||_2.
```

Hence `a_nu in G(e,p;v_0,v_n)` and `a_nu->u`.  Sequential lower
semicontinuity is lower semicontinuity because both parameter and target
are metric.

We use the controlled one-dimensional selection theorem in the following
exact form.  For a uniformly equi-`LC^0` family of subsets of a Banach
space and every `eta>0`, there is `gamma(eta)>0` such that every
lower-semicontinuous multifunction from a paracompact space of dimension
at most one, which has a continuous `gamma(eta)`-selection `g`, has an
exact continuous selection `f` satisfying

```text
f(x) in Phi(x),       ||f(x)-g(x)||<eta.               (UL8)
```

This is Gutev, *Constructing selections stepwise over skeletons of nerves
of covers*, Theorem 5.3, which gives a self-contained proof of Michael's
controlled theorem (Michael, *Continuous Selections II*, Theorem 4.1).
The function `gamma` in Gutev's proof depends only on the uniform
equi-`LC^0` modulus.  Since `(UL6)` gives one modulus for the family of
all conjugator fibres, the same `gamma` works for every `e,p,v_0`.

Fix `eta>0` and set

```text
rho(eta)=gamma(eta)/13.                                (UL9)
```

If `sup_z||v(z)-v_0||_2<rho(eta)`, then `(UL3)` says that the constant
map `g(z)=e` is a continuous `gamma(eta)`-selection for `Phi`.  Applying
`(UL8)` produces a continuous unitary loop

```text
u:S^1->U(eRe),       u(z)v_0=v(z),
sup_z||u(z)-e||_2<eta.                                 (UL10)
```

## Contract the lift and project to the Stiefel space

The hyperfinite factor `eRe` has a Popa--Takesaki contraction

```text
alpha_r:U(eRe)->U(eRe),       alpha_0=id,
alpha_infinity=e,
||alpha_r(x)-alpha_r(y)||_2<=||x-y||_2.                 (UL11)
```

View the disk as `S^1 times [0,infinity]` with its terminal circle
collapsed.  Define

```text
V(z,r)=alpha_r(u(z))v_0.
```

The contraction is jointly continuous through its terminal value `e`.
Since `u(S^1)` is compact, `alpha_r(u(z))->e` uniformly in `z`; hence the
formula is well defined and continuous at the collapsed terminal circle.
It fills the original loop and remains in the exact Stiefel fibre because
`alpha_r(u(z))` is unitary.  Finally, `(UL10)` and `(UL11)` give

```text
||V(z,r)-v_0||_2
 <=||alpha_r(u(z))-e||_2
 <=||u(z)-e||_2
 <eta.
```

Thus `(USF)` holds with the universal modulus `rho` from `(UL9)`.

The contraction used here is Theorem 1 of Popa--Takesaki,
[*The topological structure of the unitary and automorphism groups of a
factor*](https://doi.org/10.1007/BF02100051).  Its required uniform
`2`-norm inequality is also stated as Theorem 2.3 of Farah--Vaccaro,
[*Continuous Selection of Unitaries in II_1 Factors*](https://arxiv.org/abs/2501.01272).
The controlled selection theorem is Theorem 5.3 of V. Gutev,
[*Constructing selections stepwise over skeletons of nerves of covers*](https://www.math.bas.bg/serdica/2018/2018-137-154.pdf),
Serdica Math. J. 44 (2018), 137--154.
