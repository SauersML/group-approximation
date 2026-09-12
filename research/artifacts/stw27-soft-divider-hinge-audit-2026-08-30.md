# STW XXVII(2): soft-divider hinge audit (2026-08-30)

## Exact result

For a constant-rank bundle class `x=[E]` of rank `M`, an
`(n,n+1)`-divider has pointwise integer rank in

```text
[M/(n+1), M/n].
```

When `M<n(n+1)`, this interval has length less than one.  Hence every
divider has constant finite fibre rank and is Cuntz equivalent to a
projection.  The earlier mod-prime Chern obstruction therefore excludes
soft as well as compact dividers in this low-rank range.

The number `n(n+1)` is exact for this rounding mechanism.  At equality,
the module

```text
C([0,1])^n direct_sum C_0((0,1])
```

is a noncompact divider of the trivial rank-`n(n+1)` bundle.  Thus the two
Cuntz inequalities alone do not force compactness once the fibre-rank
interval contains two integers.

## Consequence for Villadsen limits

This closes the soft loophole for individual low-rank homogeneous blocks,
but it does not settle a Villadsen inductive limit.  The image rank of a
fixed seed projection grows without bound.  For a fixed `n`, every tail
eventually lies beyond `n(n+1)`, exactly where rank-jumping soft elements
become possible.  Continuity of `Cu` therefore cannot propagate the
low-rank obstruction down the whole tail.

The standard stable-rank-one reformulation makes the remaining issue
equally explicit.  For a unital stable-rank-one algebra, `(n,n+1)`
divisibility of the unit is equivalent to a unital star-homomorphism from the
prime dimension-drop algebra `Z_(n,n+1)`. An appropriately qualified
finite-stage lifting moves such a homomorphism in an inductive limit to a
sufficiently late finite stage, but at that stage the relevant bundle rank is
already unbounded. Characteristic-class
obstructions for a repeated projection divider do not automatically
obstruct the rank-jumping representation field supplied by a dimension-drop
embedding.

## Failed routes, now isolated

1. **Abstract soft-to-compact rounding.**  False beyond the sharp rank
   threshold, even over the contractible interval and for a trivial target
   bundle, by the explicit module above.
2. **External Euler test with a fixed number of Hopf lines.**  The
   Robert--Rordam tensor-test method controls arbitrary Cuntz elements, but
   for first-type Villadsen images the number of active base coordinates is
   at most the bundle rank.  Tensoring with only `n+1` auxiliary line bundles
   makes the proposed target Euler class live above the cohomological
   dimension once the stage rank is large.  The high-dimensional AH systems
   in Robert--Rordam Section 7 deliberately avoid this rank/dimension
   collapse; the ordinary first-type Villadsen tail does not.
3. **Rank functions alone.**  They give the interval above but do not decide
   Cuntz comparison in the non-strict-comparison regime.  At and above the
   threshold they permit genuine rank jumps, so a proof must control the
   topology of the resulting open-projection module or equivalently rule out
   a finite-stage dimension-drop representation field.

## Sources checked

- Robert--Rordam, *Divisibility properties for C*-algebras*,
  arXiv:1106.5523v2, Definition 3.1, Proposition 3.6, Remark 3.12, Lemma 6.1,
  and Section 7.
- Rordam--Winter, *The Jiang--Su algebra revisited*, arXiv:0801.2259,
  Proposition 5.1.
- Toms--Winter, *The Elliott conjecture for Villadsen algebras of the first
  type*, arXiv:math/0611059v1, Definitions 3.1--3.2 and Theorem 3.4.

## Independent audit

An independent adversarial audit verified the pointwise rank squeeze,
uniform spectral gap, support-projection construction, both sharp-example
comparisons, and the soft-inclusive Chern consequence. It caught and
corrected the distinction between a unital star-homomorphism from a
dimension-drop algebra and an injective embedding. The proof now also gives
a direct way-below contradiction for noncompactness of the sharp example.
