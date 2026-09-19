# STW XCV: strongly purely infinite cellular tensor audit (2026-08-30)

## Result

Every separable exact strongly purely infinite algebra tensors to a pure
algebra with every separable C*-algebra.  Thus if the other factor is pure,
this is a positive class for Problem XCV even when that factor is nonexact.
The exact strongly purely infinite factor can more concretely be assumed
purely infinite with the ideal property, or purely infinite with a
compact-open basis in its primitive ideal space.

Suppose a separable algebra `A` has a continuous ordinal ideal filtration
whose successor quotients are strongly purely infinite, and let `B` be
separable and exact.  Then `A tensor_min B` is pure.  The filtration already
implies that `A` is pure, so imposing purity on `B` gives a new positive class
for Problem XCV.

It is enough that the cells be ordinarily purely infinite with the ideal
property.  In the separable case this is equivalent to asking that their
primitive ideal spaces have bases of compact-open sets.

There is a second cellular form: if every cell is exact and strongly purely
infinite and every successor extension is cpc semisplit, the other tensor
factor is arbitrary.  This covers nonexact pure partners and nonnuclear
cells; semisplitting, rather than nuclearity, crosses the tensor-exactness
bottleneck.

## Imported theorems checked

1. Kirchberg--Sierakowski, *Filling families and strong pure infiniteness*,
   arXiv:1503.08519v2, Theorem 1.3, says that `C tensor_min D` is strongly
   purely infinite when `D` is exact and at least one of `C,D` is strongly
   purely infinite.  The source explicitly says that it does not matter
   which factor carries strong pure infiniteness.  This is imported through
   `ks-exact-tensor-strong-pi-citation`.
2. Pasnicu--Rordam, *Purely infinite C*-algebras of real rank zero*,
   J. Reine Angew. Math. 613 (2007), Proposition 2.14, proves that the ideal
   property collapses ordinary pure infiniteness to strong pure
   infiniteness.  Proposition 2.11 identifies the ideal property, for
   separable purely infinite algebras, with a compact-open basis in the
   primitive ideal space.  This is imported through
   `pasnicu-rordam-pi-ip-collapse-citation`.
3. `stw99-lxxvi-strong-pure-infiniteness-implies-cu-regularity` is already
   established in Cairn.  It identifies the Cuntz semigroup of a separable
   purely infinite algebra with its ideal lattice and proves that every
   separable strongly purely infinite algebra is pure.
4. `stw95-transfinite-exact-filtration-reduction` is already established in
   Cairn.  It assembles pure local tensor products through any continuous
   ordinal filtration of a separable algebra when the other tensor factor is
   exact.
5. `stw95-semisplit-successor-filtration-reduction` is proved in this
   package.  A cpc section produces the completely bounded projection
   `id-sq` onto the ideal; tensoring that projection proves exactness of each
   successor sequence for an arbitrary other factor.  The remaining ordinal
   induction is the same extension/Cu-continuity argument, now with no
   nuclearity hypothesis on the cells.

## Proof audit

In the direct case the Kirchberg--Sierakowski theorem is applied with the
same factor carrying both exactness and strong pure infiniteness.  The other
factor is arbitrary.  This quantifier placement was checked against Theorem
1.3: it requires an exact factor and a strongly purely infinite factor, but
they are allowed to be the same factor.

Every cell `L_alpha` is separable.  Because `B` is separable and exact, the
Kirchberg--Sierakowski theorem makes `L_alpha tensor_min B` separable and
strongly purely infinite.  The established LXXVI ideal-lattice theorem makes
each such local tensor product pure.  These are exactly the local hypotheses
of the established transfinite exact-filtration theorem, so it yields
purity of `A tensor_min B`.

Applying the same argument with the one-dimensional exact algebra `C` shows
that `A` itself is pure.  No circular appeal to the desired tensor-permanence
root is made.

In the semisplit variant, exactness and strong pure infiniteness both belong
to each cell.  Kirchberg--Sierakowski therefore makes the local product
strongly purely infinite even when the other factor is nonexact.  The new
semisplit filtration theorem then assembles these local pure products.

## Boundary and novelty checks

- In the direct theorem exactness belongs to the strongly purely infinite
  factor and the other factor is arbitrary.  In the cellular theorem
  exactness belongs to `B`; in neither case is exactness inferred from
  purity or omitted from the tensor theorem.
- The conclusion is purity, not strong pure infiniteness of the assembled
  extension.  No unproved extension permanence for strong pure infiniteness
  is used.
- The cells need not be nuclear.  Thus the Choi--Effros/ASH layered lane is
  not being reused.
- The filtration need not split and its ideals need not be central, so this
  is not the `c_0`-block theorem.  In the no-exact-partner variant only the
  quotient maps are cpc semisplit; no *-homomorphic or central splitting is
  assumed.
- A compact-open basis is zero-dimensional, not scattered.  Cantor-type
  primitive spaces are allowed inside a cell, and the cells need not be
  simple.
- No Z-absorption statement is used or concluded.  Strong pure infiniteness
  only supplies the local ideal-lattice collapse and survives tensoring
  through exactness.

This is a structural positive class, not a solution of arbitrary pure-tensor
permanence.  A counterexample can still have neither an exact strongly
purely infinite factor nor a strongly purely infinite cellular filtration
opposite an exact factor.
