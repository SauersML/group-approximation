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
`pure-representation-images-are-compact-free` proves that no representation
image of a pure algebra contains a nonzero compact operator.  Consequently
`spatial-pure-factor-reps-have-no-joint-compacts` excludes every spatial
product of factor representations, including reducible ones: a nonzero
compact slice would put a compact operator in one factor image.

There is a second, independent fence.  Takesaki's theorem makes the minimal
tensor product of simple C-star algebras simple.  Hence
`stw95-simple-pure-factors-exclude-compact-corridor` shows that a
compact-bearing counterexample must have at least one nonsimple pure factor.
Simplicity makes the irreducible representation faithful; the compact ideal
would then be the whole image, making the tensor product type I.  Type I
reflects to both factors, contradicting purity of the simple factors.

There is now a third fence covering nonsimple algebras.  If the factors are
separable and either one is exact,
`separable-exact-nowhere-scattered-tensor-permanence` proves that their
minimal tensor product is nowhere scattered.  The proof uses the
Blanchard--Kirchberg product description of the primitive spectrum: a compact
ideal in a faithful primitive quotient determines an open singleton, which
splits into open singleton ideals in the two factor quotients.  Their tensor
product is the compact ideal, so type-I reflection makes both simple factor
ideals elementary, contradicting nowhere scatteredness.  Consequently a
separable compact-bearing witness must use two nonexact factors, at least one
of which is nonsimple.

The standard property-T diagonal construction is an instructive false lead.
For an ICC property-T group, the diagonal Kazhdan projection is rank one in
the left-right image, but this is a representation of the maximal tensor
product.  Descent to the reduced/minimal tensor product is equivalent to weak
containment of the quasi-regular representation of
`(Gamma times Gamma)/Diagonal(Gamma)` in the regular representation, forcing
the diagonal subgroup to be amenable.  Hence it cannot work for an infinite
property-T group.  A compact-image counterexample must instead use a genuinely
entangled min-continuous representation with at least one nonsimple factor
and, in the separable setting, two nonexact factors.  The abstract purity of
`Cu(A) tensor_Cu Cu(B)` does not realize such a representation or identify it
with `Cu(A tensor_min B)`.
