---
rg: 2
id: stw99-xciv-relative-ii1-commutant-block-proof
kind: route
title: Put the fixed dimension-drop block in the II1 commutant of a nearby finite-dimensional algebra
target: stw99-xciv-finite-dimensional-radius-controls-block-defect
requires:
  - stw99-xciv-single-prime-block-centrality-is-exact
artifacts:
  - research/artifacts/stw99-xciv-local-fd-radius-audit-2026-08-30.md
---

Let `E subset R` be a unital finite-dimensional C*-subalgebra.  Write

```text
E~=direct_sum_(l=1)^m M_(r_l)
```

and choose matrix units `e^(l)_(ij)` with central support
`p_l=sum_i e^(l)_(ii)`.  The relative commutant decomposes as

```text
E' intersect R ~= direct_sum_(l=1)^m N_l,               (5)
```

where each `N_l` is a II1 factor with unit `p_l` (one may identify it with
the diagonal amplification of the corner `e^(l)_(11) R e^(l)_(11)`).
Every II1 factor contains a unital hyperfinite II1 subfactor and hence a
unital copy of `Z`; composing a fixed unital embedding `D=I_(2,3)->Z` gives
a unital `psi_l:D->N_l`.  Their direct sum is a unital homomorphism

```text
psi:D->E' intersect R.                                  (6)
```

Given `eta>alpha_R(F)`, choose `E` and elements `b_a in E` with

```text
||a-b_a||<eta                 (a in F).
```

For the map `(6)` and every `h in H`, contractivity gives

```text
||[a,psi(h)]||
 <=||[(a-b_a),psi(h)]||
 <=2||a-b_a||||h||
 <2 eta.                                                (7)
```

Take the maximum and then let `eta` decrease to `alpha_R(F)` to obtain
`(3)`.  Formula `(4)` is its contrapositive.

For the type-I subclass, let `M subset R` be a finite type-I von Neumann
algebra of degree at most `d`.  It is a finite direct sum of algebras of the
form

```text
L^infinity(X,mu) tensor M_r,            r<=d.
```

A finite family of essentially bounded matrix-valued measurable functions
can be approximated in essential-supremum norm by functions taking only
finitely many matrix values on a common finite measurable partition.  Those
simple functions lie in a unital finite-dimensional subalgebra of `M`.
Therefore `alpha_R(F)=0` for every finite `F subset M`.

If the elements of `F` are commuting and normal, their joint von Neumann
algebra is abelian.  Apply the preceding argument with `d=1`, equivalently
approximate their joint bounded Borel functional calculus by common finite
spectral partitions.  All approximations and commutator estimates are in
operator norm, not tracial `2`-norm.
