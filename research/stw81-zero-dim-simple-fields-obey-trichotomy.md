---
rg: 2
id: stw81-zero-dim-simple-fields-obey-trichotomy
kind: claim
title: Zero-dimensional locally trivial fields with simple fibres satisfy LXXXI
distinct_from:
  stw81-separable-subhomogeneous-positive: that requires a uniform finite bound on irreducible-representation dimensions; this permits arbitrary simple nuclear fibres, including stably finite and purely infinite non-type-I fibres, and an infinite ideal lattice.
  stw81-full-af-by-oinfinity-extensions-are-one-dimensional: that treats one full extension with stable AF ideal and O-infinity-stable quotient; this treats locally trivial fields over arbitrary second-countable zero-dimensional bases and needs no fullness or extension theorem.
  stw81-type-i-topological-dimension-collapse: that gives only a topological lower-bound consequence for general type-I algebras; this computes nuclear dimension exactly for a generally non-type-I class.
artifacts:
  - research/artifacts/stw81-zero-dimensional-simple-field-audit-2026-08-30.md
---

Let `X` be a second-countable, locally compact, zero-dimensional Hausdorff
space, and let `A` be the section algebra of a separable locally trivial
continuous C-star bundle over `X` whose fibres `A_x` are simple, separable,
and nuclear.  Then

`dim_nuc(A) = sup_(x in X) dim_nuc(A_x)`,

and this value belongs to `{0,1,infinity}`.

Moreover, for every ideal `I` of `A` and every commutative hereditary
subalgebra `C` of `A/I`,

`dim Prim(C)=0`

when `C` is nonzero.  Thus this entire class satisfies the hypothesis and
conclusion of STW Problem LXXXI.  It includes fields with infinitely many
ideals and non-type-I fibres; the conclusion is not obtained by iterating a
finite extension theorem.
