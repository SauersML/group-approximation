---
rg: 2
id: torsion-free-embedding-normal-generation-router-proof
kind: route
title: Square every generator by a stable letter, square the stable letters by one more, and hang the Baumslag--Solitar chain gadget on the free pair (d,c)
target: torsion-free-embedding-normal-generation-router
requires:
  - hnn-torsion-theorem
  - amalgam-torsion-permanence-needs-no-cyclic-reduction
---

## Imported tools (all used in-repository)

* **(HNN)** Single-letter HNN extension `G*_{phi:A->B}` for an isomorphism of
  subgroups.  The base embeds (Mathlib `HNNExtension.of_injective`), and
  Britton's lemma holds in pinch form, verbatim from
  `GroupApproximation/GroupTheory/HNNBrittonPinch.lean`:
  "`wordProd_notMem_range`, `wordProd_ne_one` — **Britton's Lemma**: a
  pinch-free word with at least one stable letter is not in the base copy,
  hence is not `1`", where a pinch is "a literal pinch `t^{u} g t^{-u}`" with
  the syllable "in the associated subgroup of its own sign".
* **(AM)** Amalgam `X *_F Y` over injective maps: each factor embeds (Mathlib
  `Monoid.PushoutI.of_injective`, used in
  `GroupApproximation/Algebra/PushoutITorsionFree.lean`).
* **(TF)** `hnn-torsion-theorem` and
  `amalgam-torsion-permanence-needs-no-cyclic-reduction`: HNN extensions and
  amalgams of torsion-free groups are torsion-free.
* **(FP)** A finite presentation plus finitely many new generators and
  relators is a finite presentation.  An HNN extension with finitely
  generated associated subgroups, or an amalgam of finitely presented groups
  over a finitely generated edge group, has such a presentation.
* **(INF)** In a torsion-free group every nontrivial `g` has `<g> ~= Z`, so
  `g |-> g^2` is an isomorphism `<g> -> <g^2>`.

## Stage A: square the generators

Put `H_0=E` and `H_i = H_{i-1} *_{t_i : <e_i> -> <e_i^2>}`.  By induction
`E` embeds in `H_{i-1}`, so `e_i` is nontrivial there.  `H_{i-1}` is
torsion-free, so `(INF)` makes this an HNN extension.  Let `H_1 := H_n`.  It
is torsion-free by (TF), finitely presented by (FP), and contains `E` by
(HNN).

**Retraction.**  Sending `E` to `1` and `t_i` to `t_i` respects every relator
(`t_i e_i t_i^-1 = e_i^2` becomes `1=1`).  This gives
`rho : H_1 -> F(t_1,...,t_n)` with `rho(t_i)=t_i`.

**Normal generation.**  Modulo `<<t_1,...,t_n>>` the relator gives
`e_i=e_i^2`, so `e_i=1`.  Hence `H_1 = <<t_1,...,t_n>>`.

## Stage B: square the stable letters

Let `T=<t_1,...,t_n>` and `T'=<t_1^2,...,t_n^2>` inside `H_1`.  `rho` maps `T`
onto `F(t)` sending `t_i` to `t_i`.  The homomorphism `F(t)->T` with
`t_i |-> t_i` composes with `rho` to the identity, so it is injective as well
as surjective.  Hence `T` is free on the `t_i`, and `rho|_T` is injective.

Likewise `rho|_{T'}` maps `T'` onto `<t_i^2> <= F(t)`.  That subgroup is
free on the `t_i^2`: a freely reduced word in the letters `t_i^{±2}` stays
freely reduced when spelled in the `t_i`.  Hence `T'` is free on the
`t_i^2`, and `rho|_{T'}` is injective.

So `phi: t_i |-> t_i^2` is an isomorphism `T -> T'`.  Put
`H_2 = H_1 *_{c : T -> T'}`.  It is torsion-free (TF) and finitely presented
(FP), and `H_1` embeds (HNN).  Modulo `<<c>>`, `t_i=t_i^2`, so every `t_i`
dies, and Stage A kills `H_1`.  Hence `H_2 = <<c>>`.

**Lemma B (the pair `(d,c)` is free).**  Take a nontrivial freely reduced
word in `d,c`.  If it contains no `c`, it is `d^m` with `m != 0`, which is
nontrivial because `E` is torsion-free.  Otherwise spell it as an HNN word
with stable letter `c`.  Its syllables between consecutive stable letters
are `1` (inside a power `c^k`, where the adjacent letters have the same
sign) or `d^m` with `m != 0` (between two `c`-powers).

A pinch needs `c^{±1} g c^{∓1}` with `g` in `T` or `T'`.  The first kind is
excluded because the signs agree.  For the second, `rho(d^m)=1` and `rho` is
injective on `T` and on `T'`, so `d^m in T ∪ T'` forces `d^m=1`,
contradicting torsion-freeness.  So the word is pinch-free, and Britton's
lemma makes it nontrivial.  Thus `<d,c> ~= F_2` on the basis `d,c`.

## Stage C: the gadget

`L=<z,y | z y z^-1 = y^2>` is `<y>*_{z:<y>-><y^2>}`, so it is torsion-free,
`y` has infinite order, and `z` has infinite order (it maps to a generator
of `L/<<y>> ~= Z`).  Put `K = L *_{x : <z> -> <z^2>}`, so
`K=<x,y,z | x z x^-1=z^2, z y z^-1=y^2>`.  It is torsion-free and finitely
presented.

* `K=<<x>>`: `x=1` gives `z=z^2`, so `z=1`; then `y=y^2`, so `y=1`.
* **Lemma C (`<x,y>` is free).**  Spell a nontrivial reduced word in `x,y`
  over the stable letter `x`.  A pinch needs `y^m in <z>` or `<z^2>` with
  `m != 0`.  Let `sigma: L -> Z` kill `y` with `z |-> 1`.  Then
  `sigma(y^m)=0` and `sigma` is injective on `<z>`, so `y^m=1`, which is
  impossible.  Britton's lemma finishes the argument.

## Stage D: amalgamate

Let `F=F(f_1,f_2)`.  Lemma B embeds `F` in `H_2` by `f_1|->d`, `f_2|->c`, and
Lemma C embeds `F` in `K` by `f_1|->x`, `f_2|->y`.  Put `P=H_2 *_F K`.
Eliminating `x=d` and `y=c` gives exactly the presentation `(EMB)`.

* `E <= H_1 <= H_2 <= P` by (HNN) and (AM), so `E -> P` is injective.
* `P` is torsion-free by (TF) and finitely presented by (FP).
* Modulo `<<d>>`: `x=d=1` kills `K` (Stage C), in particular `y=c`, and
  `H_2=<<c>>` (Stage B).  Hence `P/<<d>>=1`, that is, `normalClosure_P(d)=P`.

QED.  No small-cancellation, hyperbolicity, or Property-`(T)` input occurs.
