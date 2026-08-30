---
rg: 2
id: stw99-problem-lxxviii-zstable-map-to-quasitraceless-target
kind: claim
title: Every unital map from a simple nuclear Z-stable algebra to a quasitraceless target is O-infinity-stable (STW Problem LXXVIII)
root: true
---

**Problem LXXVIII of Schafhauser--Tikuisis--White, _Nuclear C\*-algebras:
99 problems_, arXiv:2506.10902v2.**  Let `A` be unital, simple, separable,
nuclear, and `Z`-stable, and let `B` be unital with no normalized quasitraces.
Must every unital \*-homomorphism

```text
phi : A -> B
```

be `O_infinity`-stable?

This remains open.

Every counterexample now reduces to a finite-generator target extension:
`stw78-counterexamples-have-finite-obstruction-targets` gives

```text
B_0=C*(phi(A),b_1,...,b_m)
```

with `B_0` separable and still quasitraceless, while retaining a positive
finite-set central-isometry defect.  The key compactness theorem is that
absence of normalized 2-quasitraces is witnessed by a finitely generated
unital subalgebra.

By the Blackadar--Handelman matrix criterion, the finite obstruction seed
has properly infinite unit at a least finite matrix level.  Thus
`stw78-counterexamples-have-two-finite-witnesses` reduces the open problem
to making this concrete finite matrix witness interact with the concrete
positive centralization defect.

`stw78-central-matrix-folding-descends-proper-infiniteness` proves the exact
folding step in a positive class: a central `M_n` from the domain folds a
properly infinite `M_n(C)` back into the sequence relative commutant whenever
the finite seed `C` commutes with the image.  The universal obstruction is
therefore the absence of those two interaction properties, not the folding
calculation.

If the domain has unital central matrix blocks of unbounded size and the
ordinary relative commutant contains a unital quasitraceless subalgebra,
`stw78-unbounded-central-matrices-close-relative-quasitrace-case` supplies
the matching properly infinite amplification automatically and proves the
map O-infinity-stable.  No exactness or nuclearity of the target is used.

There is now a second positive mechanism which does not inspect the relative
commutant.  `stw78-simple-comparison-targets-force-oinfinity-stability`
proves the problem whenever the target is simple and its Cuntz semigroup is
almost unperforated.  Quasitracelessness forces such a target to be purely,
hence strongly purely, infinite; nuclear-map absorption then gives
strong O-infinity-stability.  In particular every simple `Z`-stable target
is a positive class, even without target nuclearity or exactness.  Thus any
counterexample must obtain its obstruction from nonsimple or
comparison-perforated target geometry.

The nonsimple finite-ideal boundary is now exact.  Ambient normalized
quasitracelessness does not pass to nonunital layers:
`stw78-layer-quasitraces-need-not-vanish` uses the Toeplitz--Cuntz extension,
whose compact ideal has an unbounded lower semicontinuous trace even though
the nuclear unital extension algebra has no normalized quasitrace.  Thus
finite ideal lattice and almost-unperforated simple layers alone are
insufficient.

There is nevertheless a positive finite-ideal class.
`stw78-finite-ideal-regular-targets-solve-map` assumes the target is
separable nuclear and that every simple subquotient is algebraically simple
with almost-unperforated `W`.  Algebraic simplicity makes every layer
quasitrace bounded, so it extends upward and is excluded by ambient
quasitracelessness.  The layers are therefore purely infinite and
`O_infinity`-stable; Toms--Winter extension permanence glues them through a
finite composition series.  Gabe's map theorem then gives strong
`O_infinity`-stability of every nuclear map into the target.
The extension input is also recorded independently in
`stw78-nuclear-strong-pi-extension-gluing`: strong pure infiniteness glues
through finite extensions and countable increasing ideal filtrations in the
separable nuclear category.  No nonnuclear gluing claim is used.

The finite composition series can be transfinite but countable.
`stw78-countable-ordinal-regular-targets` proves the same conclusion for a
continuous ideal series indexed by any countable ordinal, with algebraically
simple almost-unperforated successor layers.  The bounded layer trace extends
through `B/I_beta` at every successor, including successors of limits.  At a
limit ordinal, a countable cofinal sequence turns continuity of the series
into a sequential inductive limit, where `O_infinity`-stability persists.
No uncountable-cofinality filtration is covered.

## Attempts

An irreducible embedding into `B(H)` is not a counterexample merely because
its ordinary relative commutant is scalar.  The definition uses the sequence
relative commutant, and
`stw99-lxxviii-essential-representation-central-o2`
records that Voiculescu absorption puts a unital `O_2` there.

The direct negative route is instead
`stw99-lxxviii-finite-target-obstruction`: find a
finite unital quasitraceless `B` containing a unital copy of some domain `A`
as above.  No such inclusion is presently constructed.  Tensoring a known
finite non-stably-finite algebra by `Z` is not a repair: in the exact simple
traceless setting, `Z`-absorption forces pure infiniteness and destroys
finiteness.

Problem LXVI is linked directly to this negative route.
`stw99-lxvi-witness-refutes-lxxviii` proves that any LXVI witness cuts down
to a finite quasitraceless CAR-containing algebra, whose unital CAR inclusion
violates `O_infinity`-stability.  Hence a positive answer here would force a
negative answer to LXVI, while a positive LXVI construction would refute this
problem.

On the positive side, `O_infinity`-stability forces every nonzero element of
the image to be properly infinite.  Establishing that conclusion from the
absence of quasitraces is already a substantive missing comparison step; even
after it, the map-level upgrade is closely tied to Problem LXXVII.
