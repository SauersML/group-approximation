---
title: Problem LXXII transfinite composition-series collapse audit (2026-08-30)
---

## Result

A weakly purely infinite C-star algebra is purely infinite whenever it has a
continuous transfinite composition series with simple successor quotients.
The series can have arbitrary ordinal length.  Neither the algebra nor its
primitive or ideal space is assumed separable, countable, Hausdorff, finite,
or linearly ordered.

## Permanence audit

The proof uses four inputs, each in the direction actually needed.

1. Weak pure infiniteness passes from an algebra to its closed ideals and
   quotients.  Thus all filtration ideals and all successor layers remain
   weakly purely infinite.
2. A simple weakly purely infinite algebra is purely infinite.  Here this is
   invoked through the established chain-ideal theorem, since a simple
   algebra has a two-element ideal lattice.
3. Kirchberg--Rordam pure infiniteness is preserved under extensions.  This
   handles every successor step once the preceding ideal and the new simple
   quotient are purely infinite.
4. The same notion is preserved under directed C-star inductive limits.
   Continuity of the filtration identifies each limit stage with the
   injective inductive limit of its predecessors, so this handles arbitrary
   limit ordinals.  No sequential-cofinality assumption is inserted.

The last two permanence results are among the main permanence theorems of
E. Kirchberg and M. Rordam, *Non-simple purely infinite C-star algebras*,
American Journal of Mathematics 122 (2000), 637--666,
DOI `10.1353/ajm.2000.0021`.  That paper's notion is the same plain pure
infiniteness used in Problem LXXII; strong pure infiniteness is not being
substituted at either step.

## Scope and examples

This genuinely extends the finite-ideal-lattice theorem but does not cover
an arbitrary weakly purely infinite algebra: existence of a continuous
simple-layer composition series is a substantial topological restriction on
its ideal structure.

The class contains nonzero examples of every ordinal length.  For an ordinal
`alpha`, the algebra `c_0(alpha,O_infinity)` has filtration
`I_beta=c_0(beta,O_infinity)`, continuous at limit ordinals and with every
successor quotient isomorphic to `O_infinity`.  When `alpha` is infinite,
arbitrary coordinate subsets produce many incomparable ideals, so these
examples lie well beyond both the finite-lattice and chain-lattice classes.
They are purely infinite (hence weakly purely infinite), either by the
transfinite theorem or directly by inductive-limit permanence.

No claim is made that every C-star algebra, every weakly purely infinite
algebra, or every algebra with a scattered primitive spectrum admits such a
series.
