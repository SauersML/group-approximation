# STW XCV general pure-tensor permanence: wave audit (2026-08-30)

## Primary-source screen

The April 2026 version of Schafhauser--Tikuisis--White,
[Problem XCV](https://arxiv.org/abs/2506.10902), continues to list arbitrary
pure-tensor permanence as open.  Searches of arXiv title, abstract, and phrase
records through 2026-08-30 found no later solution or counterexample.

The relevant current sources checked were:

- Choi--Effros, [The completely positive lifting problem for
  C*-algebras](https://annals.math.princeton.edu/1976/104-3/p08), Theorem
  3.1: completely positive contractive maps from separable nuclear
  C*-algebras lift across quotient maps;
- Antoine--Perera--Thiel, [Tensor products and regularity properties of Cuntz
  semigroups](https://arxiv.org/abs/1410.0483): tensor products in `Cu`, their
  compatibility with inductive limits, the AF external-product isomorphism
  (Proposition 6.4.13), and the characterization of pure Cu-semigroups by
  `Cu(𝒵)`-absorption;
- Perera--Thiel--Vilalta, [Extensions of pure
  C*-algebras](https://arxiv.org/abs/2506.10529): an algebra is pure exactly
  when an ideal and the corresponding quotient are pure;
- Seth--Vilalta, [Continuous functions over a pure
  C*-algebra](https://arxiv.org/abs/2602.14809), Theorem B and Remark 6.10:
  the tensor product of a pure algebra that is simple or residually stably
  finite with a unital separable ASH algebra is pure;
- Ozawa, [Proximality and selflessness for group
  C*-algebras](https://arxiv.org/abs/2508.07938), and
  Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert,
  [Selfless C*-correspondences](https://arxiv.org/abs/2607.20361): substantial
  tensor permanence for selfless inputs, but not arbitrary pure inputs.

The stronger `Cu(𝒵)`-valued assertion in the first half of XCV has already
been refuted elsewhere in this graph.  Its examples remain pure and do not
decide the general half studied here.

## One Z-stable factor

The Z-absorbing positive class does not require nuclearity of either factor.
If `A tensor Z~=A`, then minimal-tensor associativity and symmetry give

```text
(A tensor_min B) tensor_min Z
 ~= (A tensor_min Z) tensor_min B
 ~= A tensor_min B.
```

Tensoring the absorption isomorphism and its inverse with `id_B` proves the
middle equivalence without exactness of `B`.  Hence the product is Z-stable,
so its first-factor Cuntz map is an isomorphism and its Cuntz semigroup is
almost unperforated and almost divisible.  Therefore the product is pure.
This argument does not even require `B` to be pure.  In particular, both
factors of any XCV counterexample must be non-Z-stable, and the nonexact
excess-kernel mechanism cannot work after Z-stabilizing either input.

## AF-factor positive class

Let `F` be finite dimensional.  Morita invariance and finite direct sums give

```text
Cu(F) tensor_Cu Cu(B) ≅ Cu(F tensor_min B)
```

for every C*-algebra `B`.  If `C` is AF, write it as a directed inductive
limit of finite-dimensional `F_i`.  Minimal tensoring by `B`, the Cu functor,
and Cu tensoring all commute with this inductive system.  The finite-stage
isomorphisms therefore induce

```text
Cu(C) tensor_Cu Cu(B) ≅ Cu(C tensor_min B).
```

If `B` is pure, `Cu(B)` absorbs `Cu(𝒵)`.  Associativity then makes the
left-hand side absorb `Cu(𝒵)`, hence it is both almost divisible and
almost unperforated.  Consequently `C tensor_min B` is pure.  Notice that `C`
need not itself be pure, and no exactness assumption is imposed on `B`.

## The two Cu regularity axioms have different thresholds

For pure `A,B`, put

```text
S=Cu(A) tensor_Cu Cu(B),
T=Cu(A tensor_min B),
theta:S->T.
```

The abstract semigroup `S` is pure.  Almost divisibility of `T` follows from
the following internal cofinality condition alone: whenever `x'<<x` in `T`,
there are `a'<<a` in `S` with

```text
x' <= theta(a'),   theta(a) <= x.
```

Indeed, divide the pair `a'<<a` in `S` and apply `theta`.  No right inverse or
order reflection is used.

Almost unperforation has a different elementary sufficient condition: an
additive order-preserving retraction `sigma:T->S` with `theta sigma=id_T`.
Applying `sigma` to `(n+1)x<=ny` and using almost unperforation of `S` proves
`x<=y`.  Here no preservation of suprema or compact containment is required.
These criteria explain exactly which part of the stronger Cu-morphism split
criterion is used by each axiom.

## Exact finite-filtration reduction

Let `B` be exact and let

```text
0=I_0 < I_1 < ... < I_m=A
```

be a finite ideal filtration.  Exactness identifies the successive quotients
of `I_k tensor_min B` as

```text
(I_k/I_{k-1}) tensor_min B.
```

If all of these cell products are pure, repeated extension permanence makes
`A tensor_min B` pure.  If both `A` and `B` are exact with finite composition
series, a double induction reduces permanence to tensor products of their
simple composition factors.  This is a reduction, not a proof for those
simple-factor products.

## Continuous transfinite-filtration reduction

For separable filtered algebras, the same reduction extends through every
ordinal.  At countable-cofinality limits the extra input is internal:
sequential Cu colimits preserve almost unperforation and almost divisibility.
For unperforation, test the desired comparison on a compactly contained
piece, lift the resulting finite inequality to one stage, and compare there.
For divisibility, lift a way-below pair to one stage and divide it there.
Thus sequential C*-inductive limits of pure algebras are pure.

At a successor stage of a continuous ideal filtration, exactness of the
other tensor factor identifies the quotient and extension permanence
applies.  At a limit of countable cofinality, choose a cofinal sequence and
use the new inductive-limit theorem.  At a limit of uncountable cofinality, a
countable dense set in the limit ideal is already approximated inside stages
bounded strictly below that limit, so the ideal equals one earlier stage.
Hence exact pure-tensor permanence for separable algebras with arbitrary
continuous composition series reduces completely to the products of their
simple successor quotients.  No claim about those remaining simple pairs is
made.

## ASH-layered positive class

There is a second transfinite reduction that removes exactness of the tensor
factor.  If

```text
0 -> I -> E --q--> Q -> 0
```

has separable nuclear quotient, Choi--Effros gives a cpc section `s` of `q`.
The completely bounded map `P=id_E-sq` has range in `I` and is the identity
on `I`.  For every C*-algebra `A`, if `(id_A tensor q)(x)=0`, then

```text
x=(id_A tensor P)(x) in A tensor_min I.
```

Thus the extension remains exact after minimal tensoring by arbitrary `A`.
Successor extension permanence, sequential purity at countable-cofinality
limits, and separable stabilization at uncountable-cofinality limits prove:
if a continuous filtration of separable `B` has nuclear successor quotients
`L_alpha` and every `A tensor_min L_alpha` is pure, then `A tensor_min B` is
pure.  This is complementary to the exact-factor theorem: arbitrary local
layers require exact `A`, while nuclear local layers do not.

Combining this reduction with the AF-factor theorem gives a new unconditional
class.  If `A` is pure and every successor quotient `L_alpha` is AF, then all
local products `A tensor_min L_alpha` are pure and therefore
`A tensor_min B` is pure.  Unlike the earlier AF-factor theorem, the assembled
factor `B` need not be AF; unlike the ASH-layered theorem below, the AF cells
may be nonunital and `A` need not be simple or residually stably finite.  If
`B` is pure, this is a positive class for Problem XCV.

This new reduction strengthens the ASH-layered theorem.  Let `A` be pure,
with no separability or exactness assumption, and suppose either that `A` is
simple or that every quotient of `A` is stably finite.  Seth--Vilalta's
Theorem B, with Remark 6.10 for the second alternative, makes

```text
(J_(alpha+1)/J_alpha) tensor_min A
```

pure at every successor stage of an arbitrary continuous ordinal filtration
of a separable `B`.  ASH algebras are nuclear, so applying the
nuclear-successor filtration theorem proves that `A tensor_min B` is pure.
Thus if `B` is pure, this is a genuine positive class for Problem XCV; `B`
may be a transfinite extension of ASH layers rather than a single ASH
algebra, and `A` may be nonexact and nonseparable.

The qualifier “unital separable” on every ASH successor quotient is
deliberate.  It is the precise hypothesis of Seth--Vilalta's stated tensor
theorem; this audit does not silently extend that theorem to nonunital ASH
algebras.

## Nonexact excess-kernel counterexample mechanism

For an ideal `I` in `A`, let

```text
K=ker(A tensor_min B -> (A/I) tensor_min B),
E=K/(I tensor_min B).
```

The inclusion `I tensor_min B -> A tensor_min B` is injective, so `E` is an
ideal-subquotient of the tensor product.  Pureness passes to ideals and
quotients.  Therefore, for pure `A,B`, nonpureness of `E` would immediately
make `A tensor_min B` nonpure.  If `B` is exact then `K=I tensor_min B` and
`E=0`, so this mechanism is intrinsically one-sided and nonexact.

Unlike the compact corridor, `E` could in principle be nowhere scattered and
fail purity through perforation or lack of divisibility.  No example with
pure factors and nonpure `E` is known here.  Stabilizing an arbitrary
nonexactness witness by 𝒵 cannot work: it makes a factor, and hence the full
tensor product, 𝒵-stable and pure.

## Trust boundary

The AF, exact-factor filtration, nuclear-successor filtration, and
ASH-layered statements are unconditional consequences of the cited
Cu-continuity, Choi--Effros lifting, extension, and Seth--Vilalta theorems.
The excess-kernel statement is a criterion only.  No nonpure excess kernel,
failure of either purity axiom, or general tensor-permanence theorem is
claimed.
