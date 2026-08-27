---
rg: 2
id: britton-support-traps-dense-free-phase-chord
kind: claim
title: Britton support forces a dense free-phase chord to be a whole-base mapping torus
artifacts:
  - research/artifacts/britton-support-trap-for-signed-hecke-chords-2026-08-21.md
distinct_from:
  finite-character-idempotents-have-exact-hnn-transport: that gives a positive termwise transport when all coefficient support is already in the associated subgroups; this proves the converse support condition and applies it to a dense escaped signed-Hecke marginal.
  free-phase-context-support-is-a-proper-free-factor: that identifies the effective free phase group supporting the escaped context algebra; this proves that one dense escaped marginal already generates the entire effective finite-by-free packet group.
  ascending-hnn-cannot-create-nonhyperlinearity: that proves hyperlinear permanence after an HNN has been recognized as ascending; this proves that exact additive literalization forces precisely that recognition.
---

Let `B` be a group, let `A,C<=B`, let `phi:A->C` be an isomorphism, and
form the HNN extension

```text
G=<B,t | t a t^(-1)=phi(a), a in A>.                    (BST1)
```

For `x in C[B]`, if

```text
t x t^(-1) in C[B],                                     (BST2)
```

then

```text
supp(x)<=A,       t x t^(-1)=phi_*(x),                  (BST3)
```

where `supp(x)<=A` means every group-basis element with nonzero coefficient
in `x` belongs to `A`.  In particular, if

```text
t x t^(-1)=y,        <supp(x)>=B=<supp(y)>,              (BST4)
```

then `A=B=C`, `phi` is an automorphism of `B`, and `(BST1)` is the mapping
torus `B semidirect_phi Z`.  Thus it is hyperlinear whenever `B` is
hyperlinear.

This applies sharply to the free-phase signed-Hecke packet.  Let

```text
K_D=(C_2)^D semidirect S_D,       D>=3,                 (BST5)
```

let `q C[K_D]q isomorphic to M_D(C)` be its tautological block, and let
`(E_(ij))` be its matrix units.  Put `a_1=1` and let

```text
L_D=<a_2,...,a_D> isomorphic to F_(D-1),
B_D=K_D times L_D,
W=sum_i a_i E_(ii).                                    (BST6)
```

If

```text
Y=sum_(i,j)y_(ij)E_(ij)                                 (BST7)
```

has every matrix coefficient `y_(ij)` nonzero and also

```text
Tr(Y)-2y_(rr) != 0             for every r,              (BST7a)
```

then

```text
X=W Y W^*=sum_(i,j)y_(ij)E_(ij)a_i a_j^(-1)
```

satisfies

```text
<supp_(B_D)(X)>=B_D.                                    (BST8)
```

Consequently a single HNN stable letter cannot transport one such dense
escaped marginal to another base-algebra marginal while using a proper
associated subgroup.  If both endpoint marginals are dense free-phase
packets in the same effective base, exact additive transport forces the
whole-base mapping-torus case, which cannot be the decisive nonhyperlinear
signed-Hecke chord.

Such Fourier-dense self-adjoint involutions are not exceptional: in every
nontrivial signature class `0<r<D`, conditions `(BST7)` and `(BST7a)` define
a nonempty Zariski-open subset among the conjugates of
`diag(1_r,-1_(D-r))`, and one may choose an algebraic point.  Hence
sparsifying the chord sign is an actual extra resource; it cannot be silently
assumed when proposing a single infinite-edge literalization.
