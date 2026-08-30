# STW XCV general pure-tensor permanence: wave audit (2026-08-30)

## Primary-source screen

The April 2026 version of Schafhauser--Tikuisis--White,
[Problem XCV](https://arxiv.org/abs/2506.10902), continues to list arbitrary
pure-tensor permanence as open.  Searches of arXiv title, abstract, and phrase
records through 2026-08-30 found no later solution or counterexample.

The relevant current sources checked were:

- Antoine--Perera--Thiel, [Tensor products and regularity properties of Cuntz
  semigroups](https://arxiv.org/abs/1410.0483): tensor products in `Cu`, their
  compatibility with inductive limits, the AF external-product isomorphism
  (Proposition 6.4.13), and the characterization of pure Cu-semigroups by
  `Cu(𝒵)`-absorption;
- Perera--Thiel--Vilalta, [Extensions of pure
  C*-algebras](https://arxiv.org/abs/2506.10529): an algebra is pure exactly
  when an ideal and the corresponding quotient are pure;
- Ozawa, [Proximality and selflessness for group
  C*-algebras](https://arxiv.org/abs/2508.07938), and
  Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert,
  [Selfless C*-correspondences](https://arxiv.org/abs/2607.20361): substantial
  tensor permanence for selfless inputs, but not arbitrary pure inputs.

The stronger `Cu(𝒵)`-valued assertion in the first half of XCV has already
been refuted elsewhere in this graph.  Its examples remain pure and do not
decide the general half studied here.

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

The AF and finite-filtration statements are unconditional consequences of
the cited Cu-continuity and extension theorems.  The excess-kernel statement
is a criterion only.  No nonpure excess kernel, failure of either purity
axiom, or general tensor-permanence theorem is claimed.
