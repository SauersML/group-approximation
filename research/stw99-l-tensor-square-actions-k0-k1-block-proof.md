---
rg: 2
id: stw99-l-tensor-square-actions-k0-k1-block-proof
kind: route
title: Apply the graded external product to the two-vertex generator
target: stw99-l-tensor-square-actions-give-k0-k1-block
requires:
  - stw99-l-two-vertex-model-action-generates-k1
  - stw99-l-pi1-aut-splits-into-two-hom-groups
---

*Kunneth.*  `K_*(B)` is finitely generated and free, so the torsion-free
Kunneth theorem (Schochet, https://msp.org/pjm/1982/98-2/p15.xhtml) gives
`K_*(A) = K_*(B) (x) K_*(B)` with the graded bases displayed, and
`[1_A] = e_B [x] e_B = e`.  `A` is again a unital separable nuclear
simple purely infinite UCT algebra, being a minimal tensor product of
two such.

*The table.*  Write `t` for the positive generator of `K_1(C(T))`.
Equation (10) of the prerequisite says
`gammahat_*(v) = 1 [x] v + t [x] e_B` and `gammahat_*(e_B) = 1 [x] e_B`.
Applying `rho_1 = gamma (x) id`:

```text
x = v [x] e_B    ->  reduced term  t [x] e_B [x] e_B  =  e
y = e_B [x] v    ->  reduced term  0
beta = v [x] v   ->  reduced term  t [x] e_B [x] v    =  y
```

Applying `rho_2 = id (x) gamma`, the suspension class is produced in the
SECOND factor and must be moved to the front past a class of odd degree
when that factor's partner is odd:

```text
x = v [x] e_B    ->  0
y = e_B [x] v    ->  t [x] e_B [x] e_B  =  e
beta = v [x] v   ->  v [x] t [x] e_B  =  - t [x] v [x] e_B  =  -x
```

`Delta(e) = 0` for both, since `e = [1_A]` is the unit class and the
reduced class of a loop on the unit vanishes.

*Basis.*  `K_0(A)/Z[1_A] = Z beta-bar`, so
`Hom(K_0(A)/Z[1_A], K_1(A)) = Z^2` with coordinates
`((Delta beta)_x, (Delta beta)_y)`; the two loops give `(0,1)` and
`(-1,0)`, whose determinant is `1`.

Scope: Kunneth is a literature input; the sign computation is the
argument this route asserts, and it is the one place where a careless
external product would flip an entry of the final certificate.
