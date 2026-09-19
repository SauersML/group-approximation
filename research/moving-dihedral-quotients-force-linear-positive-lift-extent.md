---
rg: 2
id: moving-dihedral-quotients-force-linear-positive-lift-extent
kind: claim
title: Moving dihedral quotients force linear positive-lift extent
distinct_from:
  sl2z-central-split-inherits-operator-fejer-riesz: that gives a bounded factorization after an upstream positive lift through the fixed central amalgam has been found; this proves that positive lifts through moving relation ideals can require linearly growing extent.
  exact-core-domain-does-not-descend-to-normal-quotient: that shows a core-exact Stinespring representation can miss translated normal rows; this gives an explicit positive-polynomial family quantifying the unavoidable word growth in repairing a moving normal relation.
  finite-nuclear-quotient-does-not-complete-partial-toeplitz-data: that obstructs completion of facewise-positive data at one fixed finite nuclear target; this obstructs uniform positive lifting across a moving family even when every quotient is finite.
---

For every odd `N>=3`, let

```text
W=C2*C2=<s,t | s^2=t^2=1>,       w=st,
H_N=W/<<w^N>>=D_(2N),             q_N:C[W]->C[H_N].
```

Use reduced-word syllable extent on `C[W]`. Put

```text
c_N=(1+cos(pi/N))/2,
mu_N=(1-cos(pi/N))/2,
p_N=c_N 1+(u_w+u_w*)/2.                               (DPL1)
```

The polynomial `p_N` has extent two and uniformly bounded coefficients.
Its image is strictly positive in the finite quotient:

```text
q_N(p_N) >= mu_N 1 > 0.                               (DPL2)
```

Nevertheless `p_N` is not positive in `C*(W)`. More sharply, every
positive algebraic lift

```text
P_N in C[W],       P_N>=0,       q_N(P_N)=q_N(p_N)
```

must satisfy

```text
extent(P_N) >= N.                                      (DPL3)
```

This lower bound is genuinely about controlled lifting, not failure of
existence. A positive lift always exists and can be chosen with

```text
extent(P_N) <= 2N-2.                                   (DPL4)
```

Thus no theorem can lift quotient-positive polynomials through arbitrary
moving group-relation ideals with an extent bound depending only on the
input extent, even for scalar polynomials, finite dihedral quotients, and
the free product of two finite abelian groups covered by the 2026
operator-valued Fejer--Riesz theorem.

The missing quantitative parameter is visible: the quotient positivity
margin is

```text
mu_N asymptotic to pi^2/(4N^2).                        (DPL5)
```

A controlled lifting theorem would at least need dependence on this margin
or on the relation length. The Iwahori selector dual generally lies on a
semidefinite boundary and its normal-closure level moves, so Theorem B
alone cannot provide the required uniform translated-row correction.
The nonhyperlinear-group root remains open.

DERIVATION
moving-dihedral-positive-lift-extent-proof
