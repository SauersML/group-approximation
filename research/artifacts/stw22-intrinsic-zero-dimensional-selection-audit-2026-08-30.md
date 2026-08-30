# STW Problem XXII: intrinsic zero-dimensional factor-bundle audit

## Result audited

For every factorial tracially complete C*-algebra over a compact
zero-dimensional Hausdorff base, every trace is an integral of the
designated fibre traces and is therefore uniformly `2`-norm continuous.
The proof is in `stw22-intrinsic-weighted-selection-proof`.

## Novel scope

This strictly removes the two independent restrictions in the prior
changing-fibre results:

* `stw22-finite-derived-set-factor-bundles-have-uniform-traces` allows
  arbitrary factor fibres but only finitely many nonisolated base points;
* `stw22-expectation-fields-have-uniform-traces` allows arbitrary
  zero-dimensional metrizable bases but assumes that all fibres sit in one
  finite factor with continuously varying conditional expectations.

The new theorem assumes neither restriction.  It also removes metrizability
and includes perfect bases.  It therefore covers all countable compact
boundaries, every compact scattered boundary, and Cantor boundaries.  It
does not cover positive-dimensional Bauer boundaries or non-Bauer trace
simplices, so it is a broad positive theorem rather than a solution of the
full Problem XXII.

## Logical audit

1. **Pointwise existence.**  In a finite factor, a projection of trace
   less than `1/m` has `m` orthogonal equivalent copies.  Multiplying the
   implementing partial isometries by `a^(1/2)` gives exact weighted
   copies even when `supp(a)` jumps.
2. **Uniform correction.**  On the spectral region `[eta,1]`, inversion is
   uniformly bounded and ordinary polar correction is stable in `L^2`.
   On `(0,eta)`, the weighted operators have squared `2`-norm at most
   `eta`; no continuity of the support projection is used.  The strict
   trace slack leaves enough range for exact low-spectrum fills.
3. **Bundle locality.**  An exact fibre tuple lifts componentwise through
   `M -> M_x`.  All relation defects of those lifts are continuous scalar
   functions and vanish at `x`; the correction lemma therefore gives
   exact nearby fibre tuples close to the lifted section.
4. **Clopen gluing.**  Every finite open cover of a compact
   zero-dimensional Hausdorff space has a finite disjoint clopen
   refinement.  Central characteristic functions patch the selected
   local lifts without cross terms.  Summable errors and uniform
   `2`-completeness produce exact global weighted copies.
5. **Gap-trace estimate.**  Chebyshev makes the support of
   `(b-epsilon)_+` smaller than `1/(2m)` near a point where `b` is fibrewise
   `2`-null.  The `m` global copies give
   `m sigma((b-epsilon)_+) <= ||sigma||`; first `m->infinity` and then
   `epsilon->0` annihilate every bounded trace on the fibre gap.

## Dependency and provenance audit

The weighted correction and clopen-selection arguments are proved in full
and import no classification, selection, or bundle-triviality theorem.
The only graph dependency is the already established exact fibre-gap
criterion, used after all gap traces have been eliminated.  The nuclear
Bauer corollary uses the canonical factorial bundle of the uniform tracial
completion: compactness of the extreme boundary gives the central base,
and extremality makes the GNS fibres factors.

## Firewall

The theorem is not claimed for a base of positive covering dimension.
There, a finite cover need not admit a disjoint clopen refinement, and the
local lifted tuples cannot be patched without overlap.  The theorem also
does not claim the full non-Bauer trace problem.
