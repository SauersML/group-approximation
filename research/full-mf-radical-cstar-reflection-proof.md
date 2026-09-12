---
rg: 2
id: full-mf-radical-cstar-reflection-proof
kind: route
title: Restrict to canonical group unitaries and use the reduced augmentation criterion
target: full-mf-radical-cstar-reflection
requires:
  - universal-mf-quotient
artifacts:
  - research/full-mf-radical-cstar-reflection.md
---

Let `phi : C*_max(G) -> A` be a star homomorphism with `A` MF and put
`p=phi(1)`.  The corner `pAp` is MF: embed `A` into a norm matrix corona and
view the image of `pAp` as a C-star subalgebra.  If `v` is a unitary of
`pAp`, then `v+(1-p)` is a unitary in the ambient unital corona.  Therefore

```text
g |-> phi(u_g)
```

is, after adjoining the complementary unit, a homomorphism from `G` to an
MF group.  Full radical forces `phi(u_g)=p` for every `g`.  Density of the
complex group algebra now gives

```text
phi(x)=epsilon(x)p.
```

Thus every MF-target homomorphism kills `ker(epsilon)`.  Conversely,
augmentation itself has the MF algebra `C` as target, so the intersection of
all kernels is exactly `ker(epsilon)`.  This proves `(C1)`.

Apply the same argument to `phi : C*_r(G) -> A`.  If `phi` is nonzero, then
`p != 0` and again `phi(lambda_g)=p` for every `g`.  Choose a state on the
corner `pAp`.  Composing it with `phi` produces a state on `C*_r(G)` whose
restriction to the group algebra is augmentation.  Hence the trivial
representation is weakly contained in the left regular representation.
By the reduced augmentation criterion, `G` is amenable.  This contradicts
the hypothesis, so `phi=0`, proving `(C2)`.

A nonzero quotient of a unital C-star algebra is unital.  If a nonzero
quotient of `C*_r(G)` were MF, its quotient map would contradict `(C2)`.
Finally every separable quasidiagonal C-star algebra is MF, so a
quasidiagonal quotient must also be zero.

