# Corrected rank-20 Leavitt Hilbert-hotel construction

**Date:** 2026-08-21. **Verdict:** valid after replacing the one-cover
Shalom wrapper by a direct quotient of `St_20(R)`.  This note records every
new algebraic step; it reuses `normal-kazhdan-defect-non-mf` for the analytic
conclusion.

Let `R=L_2(F_2)` with `t_i s_j=delta_ij` and
`s0 t0+s1 t1=1`.  Put `p=s0 t0`, `q=s1 t1`.  Then

```text
p+q=1,                 t1 q s1=1,                 q!=0.       (1)
```

## The exact 20-by-20 cell

With `m=5`, define ten-by-ten block matrices

```text
U = [[s0 I, s1 t0 I], [0, t1 I]],
V = [[t0 I, 0], [s0 t1 I, s1 I]].                            (2)
```

The Leavitt relations give `UV=VU=I`.  Direct multiplication gives, for
`g in M_5(R)` and `h in M_5(F_2)`,

```text
U diag(g,I) V = diag(q I+s0 g t0,I),
U diag(I,h) V = diag(p I+q h,h).                              (3)
```

The central-coefficient restriction on `h` is essential; without it the
off-diagonal terms need not vanish.  The Whitehead identity over `M_10(R)`
puts

```text
T=diag(U,V) in E_20(R),                                      (4)
```

with an explicit elementary factorization and therefore a root-word lift
`Ttilde in St_20(R)`.

The nonunital map `psi(a)=s0 a t0` is additive and multiplicative:
`psi(a)psi(b)=s0 a(t0s0)b t0=psi(ab)`.  Hence

```text
x_ij(a) |-> x_ij(psi(a))                                    (5)
```

preserves every Steinberg relation and induces
`alpha:St_5(R)->St_5(R)`.  Let `j:St_5(R)->St_20(R)` be the upper-left
block homomorphism.  Formula (3) says that the canonical projection
`pi:St_20(R)->>E_20(R)` satisfies

```text
pi(Ttilde j(gamma) Ttilde^-1)=pi(j(alpha(gamma))).            (6)
```

Since `St_5(R)` is finitely generated, imposing (6) on one finite generating
set forces it for the whole domain.

## The moved centralizer and one full defect

Take `c=x_6,7(1)` and `lambda0=x_2,3(1)`.  Disjoint-root Steinberg relations
already make `c` centralize `j(St_5(R))`.  Applying the second formula in
(3) to `h=I+E_12` gives

```text
pi(Ttilde c Ttilde^-1)=e_1,2(q)e_6,7(1),
pi([Ttilde c Ttilde^-1,j(lambda0)])=e_1,3(q).                 (7)
```

For every `a in R`, the Steinberg relations and (1) give

```text
[x_41(a t1),x_13(q)]       = x_43(a t1 q),
[x_43(a t1 q),x_32(s1)]    = x_42(a).                        (8)
```

Weyl root permutations therefore show

```text
<<x_1,3(q)>> in St_20(R) = St_20(R).                         (9)
```

This is also the concrete instance of
`BinaryLeavittSteinberg.normalClosure_root_eq_top`.

## The finite quotient

Set `Delta=St_20(R)`.  Fix a finite generating set `S` of `St_5(R)` and let
`G` be the quotient of `Delta` by the finite transport family

```text
Ttilde j(s) Ttilde^-1 = j(alpha(s))       (s in S)            (10)
```

and the single defect-identification relation

```text
[Ttilde c Ttilde^-1,j(lambda0)] = x_1,3(q).                   (11)
```

Every added relation holds under `pi`, so `pi` factors through a surjection
`G->>E_20(R)`.  The defect survives because its image is `e_1,3(q)!=1`.
By (9), its image normally generates `G`.

Krstic--McCool applies because `R` is a finitely presented associative
unital ring and the rank is at least four; hence `Delta`, and therefore `G`,
is finitely presented.  Ershov--Jaikin-Zapirain gives property `(T)` for the
rank-5 domain and rank-20 source; the exact binary-Leavitt Steinberg instance
is also in `Steinberg/BinaryLeavitt.lean`.  Property `(T)` descends to `G`.

Thus `G` carries a Kazhdan compression core with compression domain
`St_5(R)`, stable word the image of `Ttilde`, centralizing mark the image of
`c`, and `defectNormal=G`.  Apply the existing machine-checked theorem
`normal-kazhdan-defect-non-mf` with `K=G`:

```text
Res_MF(G)=G.                                                (12)
```

Every map from `G` to an MF group is trivial, and the same is true for every
nontrivial quotient by composition with the quotient map.

## Audit corrections and trust boundary

The original useful block and fullness calculations were correct after
making the central-coefficient hypothesis explicit.  The corrected rank is
`m=5`, yielding the requested `20 x 20` Whitehead cell.  The earlier Shalom
cover wrapper had no supplied lift of the Kazhdan domain map into the cover;
it is removed.  Generator-by-generator saturation is also removed: (11) and
(9) already saturate the quotient.

Published trust boundary: Krstic--McCool finite presentability and the
Ershov--Jaikin-Zapirain property-`(T)` theorem.  The normal-Kazhdan MF-radical
step is already machine-checked in this repository.  This construction is
torsion-full and makes no non-hyperlinearity claim.  It is independent of the
Hull--Osin routing construction and of the central-sign Clifford
construction.
