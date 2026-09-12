---
rg: 2
id: hyperbolic-rf-question-equals-vtf-question-proof
kind: route
title: Fill a residual element deeply enough to turn it into invisible torsion
target: hyperbolic-rf-question-equals-vtf-question
requires:
  - relatively-hyperbolic-dehn-filling
  - hyperbolic-group-relative-to-maximal-elementary-subgroup
  - finite-torsion-carrier-virtual-torsionfree-criterion
artifacts:
  - research/artifacts/hyperbolic-rf-vtf-osin-full-proof-2026-09-11.md
---

Throughout, `R_f(X)` is the intersection of the kernels of all homomorphisms
from `X` to finite groups; it is contained in every finite-index subgroup,
because every such subgroup contains its normal core, which is the kernel of
the action on its finite coset space.
A word-hyperbolic group has finitely many conjugacy classes of finite
subgroups (Lück, arXiv:0806.3771, Theorem 7.2(v)(d), as already used by
`hyperbolic-virtual-torsionfree-via-finite-residual`), so
`finite-torsion-carrier-virtual-torsionfree-criterion` applies to every
word-hyperbolic group: it is virtually torsion-free iff `R_f` is torsion-free.

## (2) => (1)

Let `G` be word-hyperbolic and not virtually torsion-free.  By the criterion,
`R_f(G)` contains a nonidentity element of finite order, so `R_f(G) != 1` and
`G` is not residually finite.

Explicitly, if `G` were residually finite, choose finite subgroups
`F_1,...,F_r` representing all finite-subgroup conjugacy classes.  For each
element of the finite set `T = union_i (F_i minus {1})`, choose a finite
homomorphism detecting it and take their diagonal product.  Its kernel `K`
is normal of finite index.  Any nonidentity torsion element of `K` would
have a nonidentity conjugate in some `F_i intersect K`, contradicting the
choice of the product.  Thus `K` would be torsion-free.  If `T` is empty,
`G` is already torsion-free and the trivial homomorphism suffices.

## (1) => (2)

Let `G` be word-hyperbolic with `R = R_f(G) != 1`.

**Case A: `R` contains a nonidentity element `x` of finite order.**  Every
finite-index subgroup of `G` contains `R`, hence contains `x`, so no
finite-index subgroup is torsion-free.  `G` is the required group.

**Case B: `R` is torsion-free.**  Choose `1 != g in R`; it has infinite order.
Put `E = E(g)`.  By `hyperbolic-group-relative-to-maximal-elementary-subgroup`,
`G` is hyperbolic relative to `{ {1}, E }` and `<g>` has finite index in `E`.
Both peripherals are finitely generated (`E` is virtually cyclic).

*Step 1: deep normal cyclic subgroups of `E`.*  The normal core

```text
C = intersection over e in E of  e <g> e^(-1)
```

is an intersection of finitely many conjugates (`<g>` has finite index), so it
is normal in `E` and has finite index in `<g>`: `C = <g^k>` for some `k >= 1`.
For each `j >= 1`, `<g^(kj)>` is the unique subgroup of index `j` in the
infinite cyclic group `C`, hence characteristic in `C`, hence normal in `E`.

*Step 2: the filling.*  Apply `relatively-hyperbolic-dehn-filling` to the
structure `{ {1}, E }`.  Its peripheral-injectivity clause supplies finite sets
`B_1 subset {1} \ {1} = empty` and `B_E subset E \ {1}` such that any normal
`N_1 ⊴ {1}`, `N_E ⊴ E` avoiding them give a quotient that is hyperbolic
relative to the images, with `E/N_E` embedded.  Take `N_1 = {1}` and
`N_E = <g^(kj)>`.  Since `g` has infinite order, the nonidentity elements of
`<g^(kj)>` are `g^i` with `i` a nonzero multiple of `kj`; once
`kj > max({1} union { |i| : g^i in B_E })`, none of them lies in `B_E` and
`kj > 1`.  For such `j` put

```text
Q = G / <<g^(kj)>>.
```

Then `Q` is hyperbolic relative to `{ {1}, E/<g^(kj)> }`, a collection of
finite groups, and `Q` is finitely generated, so `Q` is word-hyperbolic (Osin,
arXiv:math/0510195v3, Corollary 1.2, recorded with the filling node).
In `E/N_E`, the coset `g N_E` has order exactly `kj`: for an integer `a`,
`g^a in <g^(kj)>` if and only if `kj` divides `a`.  Because `E/N_E -> Q` is
injective, its image `ḡ` also has order exactly `kj > 1`.

*Step 3: the torsion is invisible.*  Let `φ : Q -> F` be a homomorphism to a
finite group.  Composing with `G -> Q` gives a homomorphism `G -> F`, which
kills `g in R_f(G)`.  Hence `φ(ḡ) = 1`, so `ḡ in R_f(Q)`.  By the criterion,
`Q` is not virtually torsion-free.  In fact the normal-core argument alone
proves this last assertion, with no hyperbolicity assumption: every
finite-index subgroup of `Q` contains `R_f(Q)` and hence contains `ḡ`.  `QED`

## Remarks

- The integer `j` can be taken to be any sufficiently large integer, so the
  order `kj` of `ḡ` can be made divisible by any prescribed integer.
- Injectivity on a singleton `{g}` does not assert `ḡ != 1`.  The proof uses
  peripheral injectivity instead.  When using the independent finite-set
  clause of Osin's theorem to preserve a witness, use `{1,g}`.
- Case B cannot be skipped by passing to a torsion-free finite-index subgroup:
  that subgroup has the same finite residual (finite-index heredity), so it
  stays torsion-free and gives nothing.  The filling is what manufactures the
  torsion.
