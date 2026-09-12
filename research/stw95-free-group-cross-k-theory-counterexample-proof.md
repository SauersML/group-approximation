---
rg: 2
id: stw95-free-group-cross-k-theory-counterexample-proof
kind: route
title: Detect the four tensor-cross classes in the compact Cuntz branch
target: stw95-cu-z-tensor-counterexample
requires: []
---

Amrutam--Gao--Kunnawalkam Elayavalli--Patchell compute

```text
Cu(C*_r(F_2)) = N_0 disjoint_union (0,infinity],
```

with the usual mixed order and addition.  This is exactly `Cu(Z)`: the compact
branch is `N_0`, and the soft branch is `(0,infinity]`.  Thus the two factors
satisfy the hypothesis of Problem XCV.

Let

```text
D = C*_r(F_2) tensor_min C*_r(F_2) = C*_r(F_2 times F_2).
```

The free group is exact, and `C*_r(F_2)` is selfless.  Ozawa's tensor-product
theorem therefore makes `D` selfless.  A tracial selfless C*-algebra has
stable rank one.  Consequently the compact elements of `Cu(D)` are precisely
the Murray--von Neumann classes of projections, so

```text
Cu(D)_c = V(D),                 Gr(Cu(D)_c) = K_0(D).
```

Here `Gr` denotes Grothendieck completion; cancellation in `V(D)` follows
from stable rank one.

The Pimsner--Voiculescu free-group exact sequence first gives

```text
K_0(C*_r(F_2)) = Z,            K_1(C*_r(F_2)) = Z^2.
```

Apply the same sequence to the trivial action of `F_2` on
`A=C*_r(F_2)`.  Its reduced crossed product is
`A tensor_min C*_r(F_2)=D`, and every map `id-(alpha_g)_*` in the sequence is
zero.  Hence

```text
0 -> K_0(A) -> K_0(D) -> K_1(A) direct_sum K_1(A) -> 0.
```

The quotient is free abelian, so the sequence splits and

```text
K_0(D) = Z direct_sum (Z^2 direct_sum Z^2) = Z^5.
```

If `Cu(D)` were isomorphic to `Cu(Z)`, the isomorphism would preserve the
way-below relation and hence compact elements.  But

```text
Cu(Z)_c = N_0,                 Gr(Cu(Z)_c) = Z,
```

whereas the preceding calculation gives `Gr(Cu(D)_c)=Z^5`.  This is
impossible, proving `Cu(D) != Cu(Z)`.
