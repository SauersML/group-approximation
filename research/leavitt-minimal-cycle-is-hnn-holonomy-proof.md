---
rg: 2
id: leavitt-minimal-cycle-is-hnn-holonomy-proof
kind: route
title: Eliminate one carrier and read the surviving cyclic-subgroup bridge
target: leavitt-minimal-cycle-is-hnn-holonomy
requires:
  - leavitt-omega-four-cycle-compiler
  - leavitt-d3-affine-two-carrier-transport-is-absent
---

From `R0=1`, solve

```text
X=B^(-1)Y^(-1)A^(-1).
```

Substitution in `R1` gives

```text
B^(-1)Y^(-1)A^(-1) C Y D=1.
```

Multiplying the equality first by `B` on the left and then by `D^(-1)` on
the right yields

```text
Y^(-1)(A^(-1)C)Y = B D^(-1).                       (HC1)
```

This is a reversible Tietze transformation, so the original quotient is
exactly `<D,Y | Y^(-1)KY=L>` with the displayed `K,L`.

If `K,L` have the same finite or infinite order, the map
`<K> -> <L>`, `K^n |-> L^n`, is an isomorphism.  The presentation is then the
HNN extension of `D` along these two cyclic subgroups, and Britton's lemma
proves that the canonical map from `D` is injective.  Consequently mere
nonpeelability of the four-cycle is not enough: coefficient collapse demands
failure of this cyclic-subgroup matching.

For the Leavitt gates set

```text
A=1,        C=S=Omega(a,r)=1,
B=T=Omega(c,p)=h,             D=1.
```

Then `(HC1)` reads `Y^(-1)1Y=h`, hence `h=1`.  In the uneliminated form the
two relations are

```text
X Y h=1,                      X S Y=1.              (HC2)
```

They have the minimal four-cycle incidence, but neither is required to have
the direct transport shape fenced by the affine two-carrier census.  A cyclic
cover realization should therefore target `(HC2)` as a whole: one residual
must carry the target holonomy in its terminal coefficient arc, the other the
source identity in its middle arc, while the same two compound corners occur
with common orientation.  This is the structural synthesis condition for the
next word design, not a claim that a single cyclic word realizing `(HC2)` has
already been found.
