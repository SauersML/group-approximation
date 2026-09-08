---
rg: 2
id: kazhdan-criterion-inert-on-finitary-permutations-proof
kind: route
title: Project to the MF base, then restrict to the invariant support, and use the criterion twice
target: kazhdan-criterion-is-inert-on-finitary-permutation-extensions
requires:
  - normal-kazhdan-defect-non-mf
artifacts:
  - research/artifacts/finitary-linear-vs-permutation-kazhdan-criterion-2026-09-08.md
---

Let `H <= P = Sym_fin(X) x| V` with `V` MF, let `L <= H` have property (T),
and let `A ⊲ H` have property (T) with `A <= D_H(L)`.  The prerequisite is
applied twice, to two different homomorphisms out of `H`.

## 1. `A` lands in the finitary part

The projection `P ->> V` restricts to a homomorphism `H -> V`, and `V` is MF.
By the prerequisite, every homomorphism from `H` to an MF group kills a normal
property-(T) subgroup of `H` contained in `D_H(L)`, so this one kills `A`.
Hence

```text
A <= ker(H -> V) = H cap Sym_fin(X) <= Sym_fin(X).
```

## 2. `A` is finite

`Sym_fin(X)` is locally finite: a finite subset of it has supports contained
in one finite `S_0 subset X`, so the subgroup it generates embeds in the
finite group `Sym(S_0)`.  A subgroup of a locally finite group is locally
finite, so `A` is.

An infinite locally finite group is a directed union of its finite subgroups,
hence amenable, being a directed union of amenable groups.  An infinite
amenable group does not have property (T): property (T) plus amenability
forces the trivial representation to be isolated in a group whose regular
representation weakly contains it, which makes the group compact, and a
discrete compact group is finite.  Since `A` has property (T), `A` is finite.

## 3. `A` is trivial

Let `S subset X` be the union of the supports of the finitely many elements of
`A`; it is finite.  For `h in H` and `alpha in A`, normality gives
`h alpha h^-1 in A`, and the support of `h alpha h^-1` is the image of the
support of `alpha` under the permutation of `X` underlying `h`.  So that image
lies in `S`, and `S` is invariant under the `X`-action of every element of
`H`.

Restriction therefore gives a homomorphism

```text
rho : H -> Sym(S),
```

and `rho` is injective on `A`: an element of `A` acts trivially outside `S` by
construction, so if it also acts trivially on `S` it is the identity
permutation.

`Sym(S)` is finite, hence residually finite, hence MF (`mf-positive-controls`).
Applying the prerequisite a second time, now to `rho`, kills `A`.  A
homomorphism that is injective on `A` and trivial on `A` forces `A = 1`, which
is `(KI2)`.

## Where each hypothesis is used

`V` MF is step 1 and nothing else.  Property (T) of `A` is step 2 and nothing
else.  Normality of `A` in `H` is step 3, where it makes `S` invariant; note
that `A` is *not* assumed normal in `P`, and the argument never needs that.
`L` appears only through `A <= D_H(L)`, which is what lets the prerequisite be
applied at all.
