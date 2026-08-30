---
rg: 2
title: STW LXXVIII finite quasitrace-obstruction audit (2026-08-30)
kind: artifact
---

# Current literature boundary

Problem LXXVIII asks whether every unital map from a unital simple separable
nuclear Z-stable algebra to a unital algebra without normalized quasitraces
is O-infinity-stable.  The cached STW v2 source, with addenda through April
2026, still states the problem as open.  Exact-phrase and concept searches
through 30 August 2026 found no later primary source claiming a solution.

The known positive comparison is Rordam's theorem that Z-stability and
O-infinity-stability coincide for traceless separable nuclear algebras.  It
does not apply to the map target here, which need be neither nuclear nor
exact nor simple.  Bosa--Gabe--Sims--White's map theorem runs in the forward
direction from O-infinity stability to nuclear dimension and likewise does
not settle the problem.

# New finite obstruction theorem

Existence of a normalized 2-quasitrace is finitely local in the following
compactness sense: if every finitely generated unital subalgebra has one,
choose one on each finite-generated stage and take a cofinal ultralimit.
Every defining identity, including the compatible `M_2` extension, involves
only finitely many elements and therefore survives.  Contrapositively, every
quasitraceless unital algebra contains a finitely generated unital
quasitraceless subalgebra.

This is stronger than separable determination.  Given any prescribed unital
subalgebra `D subset B`, adjoining the finite obstruction seed produces an
intermediate algebra containing `D` which is still quasitraceless.  Applied
to the range of an LXXVIII map, it reduces every counterexample to

```text
B_0=C*(phi(A),b_1,...,b_m).
```

Non-O-infinity-stability survives with the same positive finite-set defect,
because the admissible isometry pairs only become scarcer when the codomain
is shrunk.

The Blackadar--Handelman matrix criterion then makes the obstruction
concrete: a unital algebra admits a normalized 2-quasitrace exactly when no
finite matrix amplification has properly infinite unit.  Thus the finitely
generated quasitraceless seed has two orthogonal isometries at a least
finite matrix level.  A counterexample can be normalized to carry
simultaneously a finite subset `F` with positive central-isometry defect and
a finite matrix proper-infiniteness witness.  The universal hinge is
precisely that these two finite witnesses need not interact.

There is a sharp positive folding mechanism when they do interact.  If the
domain central sequence algebra contains a unital `M_n`, and a unital
subalgebra `C` of the ordinary relative commutant has properly infinite
`M_n(C)`, then the commuting copies multiply to a unital map

```text
M_n(C) -> B_infinity intersect phi(A)'.
```

Two orthogonal isometries pass through this map and prove O-infinity
stability.  Thus the unresolved gap in the finite-witness normal form is not
matrix folding itself: it is moving the finite target seed into the relative
commutant and upgrading its first nonfinite amplification to a properly
infinite one.

The second issue disappears when the domain has unital central matrix blocks
of unbounded size.  If the ordinary relative commutant contains any unital
quasitraceless subalgebra `C`, Blackadar--Handelman makes `M_m(C)` properly
infinite for some `m`; choose a central `M_r` with `r>=m`.  Proper
infiniteness passes from the `m`-amplification to the `r`-amplification, and
the folding theorem proves the map O-infinity-stable.  This closes a new
positive class and leaves one precise universal obstruction: the finite
quasitrace seed in the target need not commute with the image.

# Remaining hinge

The reduction does not construct a counterexample or prove the universal
claim.  The remaining problem is now entirely separable and has a finite
quasitrace-obstruction seed.  One must either turn that finite obstruction,
together with the central Z-stability supplied by the domain, into central
Cuntz isometries, or construct a finite obstruction seed whose join with a
Z-stable image retains a finite unit.  The latter remains tied to Problem
LXVI.

# Finite-ideal extension audit

Normalized quasitracelessness of a unital algebra passes to unital quotients
by composition, but it does not exclude unbounded lower semicontinuous
quasitraces on nonunital ideals.  The Toeplitz--Cuntz extension is the sharp
nuclear example: its unital middle algebra has no trace because its `n`
orthogonal generating isometries would each have trace one, while the compact
ideal has its usual unbounded trace.  Both simple layers have
almost-unperforated Cuntz semigroup.  Hence finite ideal lattice plus regular
simple layers is not by itself a strong-pure-infiniteness theorem.

One exact repair is algebraic simplicity of the layers.  A densely finite
lower semicontinuous trace is finite on the Pedersen ideal, so on an
algebraically simple layer it is an everywhere-finite, hence bounded,
positive functional.  In a nuclear target every lower semicontinuous
2-quasitrace is a trace.  A bounded trace on an ideal extends canonically to
the containing quotient and then pulls back to the original unital target,
where it contradicts normalized quasitracelessness.  Thus every simple
almost-unperforated layer is purely infinite.

For separable nuclear layers, Kirchberg absorption upgrades simple pure
infiniteness to `O_infinity`-stability.  Toms--Winter, *Strongly
self-absorbing C-star algebras*, Transactions AMS 359 (2007), Theorem 4.3,
states exactly that `D`-stability glues across short exact sequences of
separable C-star algebras when `D` is separable, unital, strongly
self-absorbing and `K_1`-injective.  Taking `D=O_infinity` and inducting along
a maximal chain in the finite ideal lattice makes the entire target
`O_infinity`-stable.  This proves the finite-ideal positive class recorded in
the graph.  No extension permanence of strong pure infiniteness in arbitrary
nonnuclear algebras is asserted.

For completeness, the countable version uses the same absorption route.
Kirchberg--Rordam Theorem 8.6 plus Toms--Winter Corollaries 3.1--3.2 identify
separable nuclear strong pure infiniteness with `O_infinity`-stability after
stabilizing and returning from the stabilization.  Toms--Winter Corollary
3.4 preserves `D`-stability under sequential inductive limits.  Hence an
increasing exhaustive ideal filtration with strongly purely infinite
separable nuclear successive layers is strongly purely infinite.  This is a
qualified nuclear theorem, not an assertion that the matrix-diagonalization
definition glues across arbitrary extensions.

# Trust boundary

The finite-detection and counterexample-reflection proofs use only the
defining identities of normalized 2-quasitraces, a cofinal ultrafilter,
restriction to unital subalgebras, and the already proved exact
central-isometry criterion.  The two-finite-witness corollary additionally
imports exactly the Blackadar--Handelman matrix criterion characterizing
existence of a normalized 2-quasitrace by the absence of a properly infinite
unit in every finite matrix amplification.
