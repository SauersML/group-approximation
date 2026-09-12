# STW LXXVII: junk-corner quasitrace audit (2026-08-30)

## Outcome

A nonzero minimal model support `p` always gives a state on the unital corner
`pBp`; this says nothing about proper infiniteness.  The exact quasitracial
criterion is stronger:

`pBp has a normalized 2-quasitrace`

if and only if `pBp` has a nonzero stably finite quotient.  For exact corners,
Haagerup turns this into the corresponding tracial-state criterion.

Nonproperness of `p` alone does not force this criterion.  A useful positive
dichotomy reappears when the corner is simple and its Cuntz semigroup is
almost unperforated: the corner is then stably finite with a normalized
quasitrace, or it is purely infinite.  Therefore a quasitraceless corner in
this regular class is automatically purely infinite, its unit is a proper
support, and the finite-dimensional model commutant splits.

## Primary-source boundary

* Blackadar--Handelman prove that every unital stably finite C*-algebra has a
  bounded quasitrace.  Petzka, [*The Blackadar-Handelman theorem for
  non-unital C*-algebras*](https://arxiv.org/abs/1209.4547), records the
  theorem and demonstrates why nonunital analogues require care.  We apply
  only the original unital theorem, to a quotient of `pBp`.
* Haagerup, [*Quasitraces on exact C*-algebras are
  traces*](https://arxiv.org/abs/1403.7653), proves the exactness upgrade and
  explicitly lists the consequence that every stably finite exact unital
  C*-algebra has a tracial state.
* Fu--Lin, [*Nonamenable simple C*-algebras with tracial
  approximation*](https://doi.org/10.1017/fms.2021.79), Proposition 4.9,
  records Rordam's almost-unperforated simple dichotomy in the needed
  quasitracial form: a sigma-unital simple algebra with almost unperforated
  `W(A)` which is not purely infinite has nonzero quasitraces and is stably
  finite.
* Rordam, [*The stable and the real rank of Z-absorbing
  C*-algebras*](https://arxiv.org/abs/math/0408020), Theorem 4.5, proves that
  `Z`-stability gives almost unperforation.  Corollary 5.1 gives the exact
  traceless-versus-purely-infinite form.

## Why weaker hypotheses fail

Rordam, [*A simple C*-algebra with a finite and an infinite
projection*](https://arxiv.org/abs/math/0204339), constructs a nuclear simple
unital corner which is finite but not stably finite.  Its unit is not properly
infinite, while exactness and simplicity force any normalized quasitrace to be
a faithful trace and hence would force stable finiteness.  Thus this corner is
quasitraceless and traceless.  Nonproperness, nuclearity, exactness, and
simplicity by themselves do not produce a quasitrace; the comparison
hypothesis cannot be omitted from the positive dichotomy.

This also identifies the Tarski-type gap.  Failure of `2[p] <= [p]` only says
that `p` is not properly infinite.  Stable finiteness excludes paradoxicality
at every matrix level and triggers Blackadar--Handelman.  Perforation permits
a projection to be finite at level one while a matrix amplification is
infinite, exactly the behavior in Rordam's example.

## LXXVII consequence and remaining boundary

For a finite-dimensional model `D subset B`, regular simple quasitraceless
minimal corners cannot be junk: they are purely infinite, so their support
projections split and the exact finite-dimensional commutant criterion
produces central orthogonal isometries.  Repeating this locally proves
`O_infinity`-stability.

The theorem does not show that arbitrary zero-dimensional models have simple
or almost-unperforated corners.  A surviving counterexample must force a
nonproper minimal support whose corner either has a stably finite quotient
(and hence a quasitrace), or lies outside the regular simple comparison class.
No assertion is made that corner quasitraces extend quasitracially to `B`.
