# Problem LXXIII literature audit (2026-08-30)

## Scope and verdict

Exact-title, exact-phrase, author, and Cuntz-semigroup searches were run for
work available through 2026-08-30.  No paper claiming the unrestricted result
or a counterexample was found.  This negative search result is not itself a
proof of absence.  The strongest current-status evidence located is Eduard
Vilalta's survey of 2025-12-15, which explicitly says that the Global Glimm
Problem remains open and identifies ideal-filteredness and property (V) as the
remaining Cuntz-semigroup issues.

Primary sources checked:

- H. Thiel and E. Vilalta, *The Global Glimm Property*,
  <https://arxiv.org/abs/2204.13059>.  Theorem 7.1 characterizes the property
  by nowhere scatteredness, ideal-filteredness, and property (V); Problem 7.2
  records the remaining general problem.
- P. W. Ng, H. Thiel, and E. Vilalta, *The Global Glimm Property for
  C*-algebras of topological dimension zero*,
  <https://arxiv.org/abs/2507.16261>.  This proves the result for topological
  dimension zero, not in general.
- E. Vilalta, *An introduction to the Global Glimm Problem*,
  <https://arxiv.org/abs/2512.13334>.  The survey still calls the general
  problem open, lists the known low-dimensional and stable-rank cases, and
  asks whether every Cuntz semigroup has property (V) and whether nowhere
  scatteredness forces ideal-filteredness.

## New progress recorded in this repository

The direct route `finite-square-zero-packet-proof` proves, for the precise
hypothesis used in Problem LXXIII (the algebra itself has no nonzero
finite-dimensional representations), that finitely many exact square-zero
elements always suffice to cover the prescribed cutdown at the level of
generated ideals.  This does not assume that every hereditary subalgebra is
nowhere scattered.

The proof exposes a sharply local remaining obstruction: finite cutdown
fusion.  The corresponding open claim is
`finite-square-zero-packets-admit-cutdown-fusion`.  The chain-ideal-lattice
case collapses the packet without any fusion theorem and is therefore an
unconditional new positive case.

There is now also a local support-preserving destabilization theorem.  It is
enough that the reserved spectral cutdown lie in *some* C-star subalgebra
`B` whose multiplier unit is properly infinite.  The finite packet is built
inside `B`; a multiplier Cuntz pair then embeds `M_2(B)` into a corner of
`B`.  Applying it to one-stabilization packet fusion sends
`h tensor e_11` to `s_1 h s_1^*`.  Since generated ideals are invariant under
multiplier multiplication, compression by `s_1^*` and `s_1` recovers the
original `h` in the returned nilpotent's ideal.

The host can depend on the cutdown.  Taking `B=A` recovers the global
properly-infinite-multiplier theorem, hence the stable and properly infinite
unital cases, but the local form is strictly broader.  For example, let
`D=C_0((0,1]) tensor K` and let `A` be its unitization.  The algebra `D` is
stable and projectionless; stability gives it a properly infinite multiplier
unit, whereas
`1_A` is finite: the defect of an isometry in `A` lies in the projectionless
ideal `D` and must vanish.  Every cutdown supported in `D` still has `D` as a
local host.  This example demonstrates strictness of the cutdown theorem;
its scalar quotient means that it is not itself a global LXXIII example.

Consequently a global counterexample must contain a nonzero spectral cutdown
which lies in no C-star subalgebra with properly infinite multiplier unit.
In particular, both the multiplier unit of its generated hereditary
subalgebra and that of its generated ideal fail to be properly infinite.

## Continuous-trace counterexample stress test

A natural counterexample search is to use a continuous-trace algebra over an
infinite-dimensional compact base with nontorsion Dixmier--Douady class.  The
route `full-square-zero-gap-dd-torsion-proof` identifies a mandatory pathology
for any full square-zero element in such an algebra: its fiberwise singular
spectra must crowd every level below the uniform top singular value.  A single
uniform gap would cut out a full finite-rank projective corner and force the
Dixmier--Douady class to be torsion.  Consequently, a proposed counterexample
cannot be certified merely by the absence of finite-rank twisted bundles; it
must also rule out square-zero sections with spectral bands born and dying
across the base.  This is a rigorous obstruction to the most direct
projection-extraction argument, not a claimed counterexample.

## Exact two-packet obstruction

The established claims `square-zero-cover-is-orthogonal-pedersen-pair` and
`finite-packets-fuse-after-one-stabilization` locate the algebraic obstruction
without approximation language.  A finite packet always becomes one exact
nilpotent in `M_2(A)`.  Returning it to `A` is equivalent to producing in `A`
an orthogonal Pedersen-equivalent positive pair whose common ideal contains
the reserved cutdown.  Scalar addition fails because of mixed products, and
matrix stabilization removes those products by putting source and range in
orthogonal corners.  Any proposed general proof must therefore supply this
orthogonal pair intrinsically in `A`; merely perturbing an almost-nilpotent
does not by itself control the generated ideal.
