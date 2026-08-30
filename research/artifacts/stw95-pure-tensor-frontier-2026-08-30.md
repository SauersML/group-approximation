# STW Problem XCV pure-tensor frontier (2026-08-30)

## Literature status

The May 2026 version of Schafhauser--Tikuisis--White still states that tensor
products of pure C-star algebras are open.  Searches through 2026-08-30 found
no later general solution or counterexample.

The strongest recent positive mechanisms checked were:

- N. Ozawa, *Proximality and selflessness for group C*-algebras*,
  <https://arxiv.org/abs/2508.07938>, version 8 dated 2026-04-24.  Exact
  selfless tensor products are selfless.
- D. Gao, M. Junge, S. Kunnawalkam Elayavalli, G. Patchell, and L. Robert,
  *Selfless C*-correspondences, operator valued C*-probability spaces and
  completely positive maps*, <https://arxiv.org/abs/2607.20361>, submitted
  2026-07-22.  Among other extensions, a selfless factor tensored with an
  exact simple uniquely tracial factor is selfless.  The paper does not claim
  arbitrary pure-tensor permanence.
- L. Robert, *Selfless C*-algebras*,
  <https://arxiv.org/abs/2309.14188>, version 3 dated 2025-06-06, for the
  regularity consequences of selflessness.

The established `stw95-cu-z-tensor-counterexample` refutes only the stronger
claim that two factors with Cuntz semigroup `Cu(Z)` have tensor Cuntz
semigroup `Cu(Z)`.  Its tensor products remain pure.

## New positive criterion

`split-cu-tensor-map-implies-pure-product` proves that it is enough for the
canonical map

```text
Cu(A) tensor_Cu Cu(B) -> Cu(A tensor_min B)
```

to have a Cu-morphism right inverse.  The abstract tensor product is pure by
`Cu(Z)`-absorption, and almost unperforation and almost divisibility pass
directly to a Cu-retract.  This is strictly weaker than requiring the
canonical map to be an isomorphism.

There is also unconditional local divisibility on the concrete tensor:
`finite-elementary-tensor-blocks-are-divisible` shows that every finite sum
of elementary tensor classes, with compact containment lifted in one pure
factor, admits the required `n` versus `n+1` divisor.  Therefore a failure of
almost divisibility must be carried by an entangled positive class for which
inner approximation by the canonical Cu tensor image breaks down.

## New counterexample engine and its tensor-norm fence

`entangled-compact-image-obstructs-tensor-purity` shows that a
compact-bearing irreducible representation of the minimal tensor product
creates an elementary ideal-subquotient and therefore destroys purity.
`spatial-pure-factor-reps-have-no-joint-compacts` proves that no spatial
product of irreducible factor representations can do this: a nonzero compact
slice would put a compact operator in an irreducible image of a pure factor.

The standard property-T diagonal construction is an instructive false lead.
For an ICC property-T group, the diagonal Kazhdan projection is rank one in
the left-right image, but this is a representation of the maximal tensor
product.  Descent to the reduced/minimal tensor product is equivalent to weak
containment of the quasi-regular representation of
`(Gamma times Gamma)/Diagonal(Gamma)` in the regular representation, forcing
the diagonal subgroup to be amenable.  Hence it cannot work for an infinite
property-T group.  A compact-image counterexample must instead use a genuinely
entangled min-continuous representation, and current exact-selfless
permanence points toward nonexact factors.
