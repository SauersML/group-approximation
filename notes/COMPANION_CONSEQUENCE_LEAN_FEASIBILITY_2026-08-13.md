# Companion-consequence Lean feasibility — 2026-08-13

This is an audit note, not part of the manuscript. It separates mathematical
validity from availability of unconditional, semantically exact formal
counterparts.

## Results already matched without literature premises

- Operator-MF is closed in every fixed-rank marked-group space, and every
  non-MF point has a finite word-ball cylinder contained in the non-MF locus.
- The chosen finitely presented non-MF witness has a nonempty finite clopen
  cylinder contained in the non-MF locus.
- There is a finite universal Horn sentence which holds in every operator-MF
  group and fails in the chosen finitely presented witness.
- The chosen witness remains finitely presented and non-MF after free product
  with the infinite cyclic group.

For the literal printed presentation, the word-length bounds 16 and 34 are
checked, but the non-MF cylinder and the literal free-product endpoint retain
the same property-(T) boundary as the literal main endpoint. They must not be
presented as unconditional formal matches until that boundary is closed.

## Mathematically valid companion deductions not presently formalizable 1:1

The proposed exact/simple/unique-trace consequences have sound published
inputs:

- Guentner--Higson--Weinberger prove that every linear group is exact.
- Kirchberg--Wassermann prove that exact groups are closed under extensions.
- Dykema proves that exact groups are closed under free products.
- The Powers--Paschke--Salinas free-product criterion says that a nontrivial
  free product is C-star simple unless it is `Z/2 * Z/2`.
- Breuillard--Kalantar--Kennedy--Ozawa prove that every C-star-simple discrete
  group has the unique-trace property.

These inputs do imply the companion note's claims about `W * Z` and `E * Z`.
However, the present Mathlib snapshot has no APIs for group or C-star
exactness, C-star simplicity, reduced free-product C-star algebras, or
uniqueness of trace. Under the project's no-premise-laundering rule, adding
the operator-algebraic conclusions to the manuscript would require
formalizing the missing theories and the cited theorems, not packaging them
as structures or hypotheses. The strongest current unconditional formal
endpoint is therefore the group-theoretic chosen-witness free product.

## Computability boundary

The computability modules prove the pullback argument from an explicitly
supplied computable Adian--Rabin reduction. They do not construct a syntax of
finite presentations or the Adian--Rabin transformation. Likewise, the
group-C-star recognition module is deliberately parametric because Mathlib
has no maximal group C-star algebra API. Thus the manuscript's Adian--Rabin
and group-C-star recognition theorems are supported by their cited classical
sources, but do not yet have unconditional one-to-one formal counterparts.

## Strongest truthful integration order

1. Keep generic marked closedness, the chosen clopen cylinder, and the chosen
   Horn separator in the manuscript with exact theorem-level margin links.
2. The literal property-(T) endpoint is now unconditional; literal
   consequences may cite `LiteralNonMFEndpoint.manuscriptTheoremA` directly.
3. Add only the chosen group free-product consequence if a new consequence is
   wanted before additional foundations are built.
4. Do not add exactness, C-star simplicity, monotraciality, or unconditional
   Adian--Rabin badges until their semantic foundations and external theorems
   are actually formalized.
