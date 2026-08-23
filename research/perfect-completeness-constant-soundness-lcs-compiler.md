---
rg: 2
id: perfect-completeness-constant-soundness-lcs-compiler
kind: claim
title: A computable LCS family with perfect commuting completeness on halting inputs and strict matrix soundness on nonhalting inputs
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - research/artifacts/published-nonhyperlinear-shortcut-audit-2026-08-21.md
  - research/artifacts/lin-ji-mastel-slofstra-bcs-lcs-boundary-2026-08-23.md
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
distinct_from:
  taller-vidick-lcs-re-hardness: that theorem has completeness `1 - epsilon` and its decoder needs the noise; this asks for `epsilon = 0`, which the paper explicitly does not prove.
  hs-pcp-boone-compiler: that asks for matrix soundness on halting inputs with an infinite exact side on nonhalting inputs (coRE orientation); this asks for perfect commuting completeness on halting inputs and strict matrix soundness on nonhalting inputs (RE orientation), which is the orientation in which MIP* soundness is already available.
  bcs-to-lcs-exact-support-gap: that asks for an exact LCS sub-menu of one fixed tracial BCS with approximate soundness; this asks for a machine-indexed family whose halting-side solution-group mark is nontrivial.
---

Construct a computable map `M -> L_M` from Turing machines to finite
binary linear constraint systems, with solution groups `Gamma_M` and
central involutions `J_M`, such that

```text
M halts          =>  J_M != 1 in Gamma_M
                     (equivalently omega^co(L_M)=1),                    (PC1)
M does not halt  =>  omega_q(L_M) < 1.                                 (PC2)
```

By `re-oriented-lcs-compiler-gives-nonhyperlinear-group` this effectively
yields an explicit nonhyperlinear solution group `Gamma_(M_*)` for a
proof-search fixed-point machine `M_*`.  Taller--Vidick prove the stronger
uniform `(PC2)` bound `omega_q<=71/72` and a version of `(PC1)` with value
`1 - epsilon` only.

## Published perfect-gap CSPs stop exactly before LIN

Culf--Mastel, arXiv:2410.21223v2, do supply the right recursion-theoretic
orientation *before* the syntax conversion.  Their finite oracular 2-CSP
family has perfect CE completeness on halting inputs and a constant
finite-dimensional/CE soundness gap on nonhalting inputs; this is recorded in
`culf-mastel-oracular-2csp-perfect-gap-family`.  The output relations are
general nonaffine 2-CSP relations (equivalently one may use their
NP-complete Boolean languages or 3-colouring), not linear equations.

The Paddock--Slofstra BCS reductions do not cross this last boundary.  Their
Lemma 5.4 compiles a source relation `R` into a target language `L` only when
`R` is pp-definable from `L`.  A relation pp-definable from `LIN` is affine:
the defining parity equations have an affine solution set, and projection
along the existential auxiliary coordinates remains affine.  Hence a
nonaffine Culf--Mastel predicate is not eligible for the Lemma 5.4 reduction
with target language `LIN`.  Their Lemma 5.5 runs in the opposite direction:
`LIN` is definable from every non-Schaefer language, so it compiles an
already-linear source *out to* the NP-hard language.  It does not compile an
NP-hard CSP back to an LCS.  Proposition 5.8 then identifies a
tracial/non-`R^U` LIN instance itself with the existence of a finitely
presented nonhyperlinear group; it is an endpoint equivalence, not a generic
BCS-to-LCS reduction.

Slofstra's solution-group embedding theorem (arXiv:1606.03140, Theorem 3.1)
also starts one step too late.  Its input is a finitely presented **group**
with a specified central involution, and its output is a solution group into
which that group embeds while preserving the involution.  A 2-CSP/BCS algebra
is presented instead by vanishing joint spectral projections.  The theorem
does not convert those additive projection relations into group relators.
Moreover, an embedding preserves exact nontriviality and lets exact target
representations restrict to the source group, but by itself supplies no
decoder from almost representations to a near-perfect CSP strategy.  Thus
the Culf--Mastel soundness gap cannot be fed directly into the theorem.

The exact remaining bridge can therefore be stated without a uniform gap.
For the Culf--Mastel instance `B_M`, construct effectively a finitely
presented group `G_M`, a central involution `j_M`, and an ultraproduct decoder
such that

```text
M halts and B_M has a perfect CE model  =>  j_M != 1 in G_M,
an approximate representation sequence of G_M
  with j_M separated from 1             =>  a perfect CE model of B_M.
```

On a nonhalting input the second implication contradicts their constant
soundness theorem, so `j_M` is trivial in approximate representations.
Slofstra's effective embedding can then turn `(G_M,j_M)` into an LCS family
satisfying `(PC1)--(PC2)`: a hypothetical separated approximate
representation sequence of the solution group restricts, through the fixed
embedding words, to one of `G_M`.  This mark-relative CSP-to-group
ultraproduct decoder--equivalently a direct perfect LCS compiler--is the
missing theorem.  None of the three cited published reductions supplies it.

## A direct qutrit group route now bypasses, but does not solve, LIN

There is now a strictly local alternative to binary affine lowering.
`non-ce-bcs-has-positive-one3-weighted-form` specializes the Culf--Mastel
machinery to a fixed positive-ONE3 system while preserving the tracial/non-CE
separation and every selected global-variable moment.  Then
`positive-one3-is-one-qutrit-clock-context` identifies each local clause
algebra exactly with one order-three clock.  No local nonlinear predicate
remains.

This does **not** establish the present LCS claim.  Repeated occurrences of a
Boolean variable now demand equality of one spectral projection of two
qutrit clocks, not equality of the clocks themselves.  Literal group-algebra
equality is too strong, commuting finite-phase auxiliaries remain affine,
and `qutrit-psync3-tensor-closure-obstruction` refutes even the proposed
noncommutative complement-flexible
`qutrit-fixed-space-projector-synchronizer`.  The remaining qutrit output is
the five-edge overlap normal form
`qutrit-diamond-robustly-synchronizes-pvms`; wordizing those overlaps joins
the independent-set route at
`hybrid-rank-router-authenticates-affine-overlap-blocks`.  Thus this splice
narrows groupification but should not be counted as either a proof of this
machine-indexed binary LCS compiler or a separate direct terminal.

## Attempts

- **Remove the mask from the Taller--Vidick decoder.**  Dies by
  `linear-encoding-lcs-admits-odd-subset-cheats`: without noise every
  linear test on a linear encoding is passed by odd-subset characters with
  consistent marginals, so the decoder has nothing to decode unless the
  odd-subset relaxation of the source is itself unsatisfiable.  The
  Fourier damping `(1-2epsilon)^|beta|` is what suppresses `|T| >= 3`.
- **Correlate the mask while keeping perfect completeness.**  Dies by
  `perfect-correlated-masks-have-undamped-conditioned-spectrum`.  The exact
  completeness constraints are nonnegative linear equations and force the
  mask law to be supported on functions equal to one on every honest atom.
  All Fourier characters surviving the source conditioning are therefore
  identically one.  If only a smaller honest support `S` is protected, the
  best decoder constant is at most `1/|S|`, exactly the repeated source's
  random-guessing floor.
- **Nonlinear gadgets inside the LCS.**  Dies at the algebra level:
  distinct cosets of `<J>` are linearly independent in `C[Gamma]/(J+1)`, so
  commuting group-element involutions satisfy only affine joint-spectrum
  constraints (`regular-trace-blocks-exact-local-predicate-return`,
  `central-pinning-forbids-nonlinear-predicates`).  Encoded variables must
  be non-group-element functions, and then cross-context consistency is
  an algebra relation that only tests, not relators, can impose.
- **Live direction: make the odd-subset relaxation hard.**  The target
  is a source family `B_M` whose odd-subset relaxation (consistent
  families of odd subsets of satisfying assignments, with mod-2 marginal
  agreement) is still robustly unsatisfiable in finite dimensions on
  nonhalting inputs, while honest tracial solutions survive.  A
  self-reducing family, whose relaxation is again an instance of the
  family, would inherit soundness.  This is where the programme's
  self-similarity idea has a precise job.
- **Encodings cannot create hardness.**  Odd subsets of an affine set have
  affine parity, so the odd-subset relaxation of a *linear* source is the
  source itself, while for a nonlinear source with single-variable overlaps
  it collapses every `S_C` to its affine hull.  Rich overlaps pin odd
  subsets to points (three assignments cannot pairwise agree off every
  coordinate) but push the contexts toward pairwise commutation, which is
  classical.  Hence a noise-free linear encoding is sound only when the
  source is already an LCS with the gap: the gap must be **native** to a
  solution group.  Native gap amplification for an LCS with `J = 1` is the
  statement `||J(U) - I||_2 <= C Def(U)` with `C` independent of the area
  of `J`, i.e. HS length control for the word `J`
  (`hs-dehn-modulus-bounded-by-dehn-function`).  So the three frontier
  formulations -- this claim, `hs-pcp-boone-compiler`, and
  `unsolvable-word-problem-group-with-computable-hs-dehn-modulus` -- are
  one problem: a robust non-abelian Gaussian elimination, in which a
  derivation of `J = 1` through non-commuting variables, of unbounded
  area, is forced on every approximate finite-dimensional solution at
  constant cost.  Classical 3-XOR has this (expansion plus linear algebra)
  because abelian refutations have area at most the number of equations;
  the non-abelian derivation is where area escapes, and
  `centralized-cyclic-distortion-hs-dehn-tracks-area` is the model of how.
- **Orientation check.**  Do not try to obtain `(PC1)` from Lin's
  `MIP^co = coRE` compiler: its exact side is the commuting side on
  nonhalting inputs, which is the other orientation
  (`kleene-mipco-self-destroying-game`).
- **Reverse Kleene does not manufacture perfect completeness.**
  `reverse-kleene-does-not-remove-tv-completeness-loss` runs the exact
  self-referential proof search for `J=1`.  The NONHALT branch would close the
  goal, but a HALT proof gives only an instance-dependent upper gap
  `gamma(D)` and conflicts with completeness `1-epsilon` only if
  `epsilon<gamma(D)`.  Since `epsilon` was fixed before `D` is found, this is
  another threshold-crossing obligation.  At `epsilon=0` the Bernoulli mask
  support collapses and the Taller--Vidick decoder becomes vacuous, so no
  algebraic limiting argument repairs it.
- **2026 shortcut audit.**  Cleve--Culf--Taller, arXiv:2607.06876, now give
  RE-hard tilted-XOR games, but their inherited completeness is
  `3/4-epsilon`, not one.  Culf, arXiv:2603.14746, rounds almost-perfect
  projection strategies to approximately tracial strategies; it does not
  create a perfect commuting LCS solution.  Neither result supplies
  `(PC1)`, and Taller--Vidick v2 still explicitly identifies `epsilon=0` as
  the nonhyperlinear-group threshold.

**Note (2026-08-22 audit).**  `linear-encoding-lcs-admits-odd-subset-cheats`
is OPEN again: its global statement fails for sources with non-extendable
local assignments (`odd-subset-relaxation-needs-local-extendability`);
any "encodings cannot create LCS hardness" / "dies by the odd-subset
cheat" reasoning here holds only under local extendability of the source.
