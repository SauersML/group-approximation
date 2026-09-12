---
rg: 2
id: stw84-finite-stabilizer-menu-field-proof
kind: route
title: Purify finitely many stabilizer lattices and resolve the central stabilizer field
target: stw84-finite-stabilizer-menu-wreath-bound
requires:
  - stw84-directed-union-uniform-bound
  - stw84-abelianization-rank-lower-bound
artifacts:
  - research/artifacts/stw84-finite-stabilizer-menu-wreath-2026-08-30.md
---

We use the finite-stage framework and notation of Eckhardt--Wu Theorem 5.1
and equation `(5.1)`, together with their strongly outer twisted-crossed-
product argument.  The new input is an elementary simultaneous purity
lemma for finitely many subgroups of a finitely generated abelian group.

## Step 1: isolate exactly the stabilizer directions acting trivially

Let `F<=L` be finite, let `V<=A` be finitely generated of rational rank
`q`, and let `T<=S` be a countable `V`-invariant set.  Put `D=C*(F)` and

```text
Omega=Spec Z(D^(tensor T)).
```

The space `Omega` is zero-dimensional.  Fix `x in Omega` and `N<=V_x`.
The fiber `D_x` is a tensor product of the full matrix blocks selected by
`x` at the sites of `T`.

Call a type `H_i` active if there is a site `t in T` with `A_t=H_i` whose
`N`-orbit supports a non-scalar matrix factor in `D_x`.  Set

```text
J=intersection_(i active) (N intersection H_i),          (FSP1)
```

with `J=N` if there is no active type.  Every element of `J` fixes every
non-scalar tensor coordinate; permutations of scalar coordinates act
trivially.  Hence `J` acts trivially on `D_x`.  It is central in `N` because
`N` is abelian.

Consequently `D_x rtimes N` is a `C*(J)=C(J_hat)`-algebra.  The central map
is injective in the reduced crossed-product picture because all groups are
amenable.  Its fiber at `chi in J_hat` is

```text
D_x rtimes_(alpha_bar,omega_chi) M,      M=N/J,          (FSP2)
```

where the scalar cocycle records the central extension.  This is an upper-
semicontinuous `J_hat`-C*-algebra in the precise sense needed for the
general separable field inequality; no norm-continuity of the bundle is
assumed.

For each active type put

```text
P_i=(N intersection H_i)/J <= M.
```

There are finitely many such subgroups and

```text
intersection_(i active) P_i=0.                           (FSP3)
```

## Step 2: a simultaneous pure-sublattice lemma

Let `M` be any finitely generated abelian group and let
`P_1,...,P_k<=M` have zero intersection.  Choose a free subgroup `M_0<=M`
of finite index.  For

```text
Q_i=M_0 intersection P_i
```

let

```text
bar(Q_i)={u in M_0 : n u in Q_i for some n>=1}
```

be its saturation.  The finite group `bar(Q_i)/Q_i` has a finite exponent.
Choose a common multiple `d` of these finitely many exponents and put

```text
K=dM_0.                                                   (FSP4)
```

Then `K` is torsion-free and finite-index in `M`, and

```text
K intersection P_i=d bar(Q_i).                           (FSP5)
```

Indeed, if `dy in P_i` with `y in M_0`, then `dy in Q_i`, so
`y in bar(Q_i)`; the reverse inclusion follows from the choice of `d`.
The saturated subgroup `bar(Q_i)` is pure in the finite-rank free group
`M_0`, hence a direct summand.  Scaling by `d` shows that
`K intersection P_i` is pure in `K`.

Apply this lemma to the subgroups in `(FSP3)`.  If `0!=k in K`, choose an
active `i` with `k notin P_i`.  Purity says that the class of `k` in
`K/(K intersection P_i)` has infinite order.  Therefore `k` has an infinite
orbit on the homogeneous `M`-orbit with stabilizer `P_i`.  By activity, that
orbit carries one fixed non-scalar matrix block.  The induced automorphism
of `D_x` thus contains an infinite homogeneous tensor shift and is strongly
outer.  This holds for every nonzero `k in K`.

## Step 3: bound every twisted fiber

If `K!=0`, the strongly outer twisted-crossed-product theorem places the
crossed product by `K` in the simple monotracial nuclear `Z`-stable class
used by Eckhardt--Wu.  Since `M/K` is finite, their finite-quotient argument
shows that every algebra in `(FSP2)` is a finite direct sum of such algebras
and therefore has nuclear dimension at most one.

If `K=0`, then `M` is finite.  The tensor product `D_x` has an increasing
dense union of finite-dimensional `M`-invariant coordinate algebras: enlarge
each finite coordinate set by its finite `M`-orbit.  Their scalar-twisted
crossed products by `M` are finite-dimensional, so `(FSP2)` is AF and has
nuclear dimension zero.  This includes the scalar case: when no type is
active, `J=N`, `M=0`, and `D_x rtimes N=C*(N)` is accounted for entirely by
the base `N_hat`.

Since

```text
dim(J_hat)=rank_Q(J)<=q,
```

the upper-semicontinuous field inequality applied to `(FSP2)` gives

```text
dim_nuc(D_x rtimes N)+1 <= 2(rank_Q(J)+1)<=2(q+1).       (FSP6)
```

Eckhardt--Wu Theorem 5.1 and `(5.1)`, with `dim(Omega)=0`, now yield

```text
dim_nuc(D^(tensor T) rtimes V)+1
 <=2(q+1)9^q.                                           (FSP7)
```

## Step 4: exhaust the countable wreath product

Choose increasing finite subgroups exhausting `L`, increasing finitely
generated subgroups exhausting `A`, and invariant hulls of increasing finite
subsets of `S`.  The point stabilizers at a `V`-stage are among

```text
V intersection H_1,...,V intersection H_m,
```

so the same finite-menu proof applies.  The stage ranks satisfy `q<=r`.
For `r>=1`, `(FSP7)` and `stw84-directed-union-uniform-bound` give the upper
bound in `(FSM2)`.  Killing all lamps gives a quotient onto `A`, and
`stw84-abelianization-rank-lower-bound` gives the lower bound `r`.

If `r=0`, the abelian actor `A` is locally finite.  The lamp group is
locally finite, and its extension by `A` is locally finite.  Thus `C*(G)` is
AF and `(FSM3)` follows.
