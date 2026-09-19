---
rg: 2
id: perfect-completeness-constant-soundness-lcs-compiler
kind: claim
title: A computable LCS family with exact finite-dimensional completeness on halting inputs and constant soundness on nonhalting inputs
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - research/artifacts/published-nonhyperlinear-shortcut-audit-2026-08-21.md
distinct_from:
  taller-vidick-lcs-re-hardness: that theorem has completeness `1 - epsilon` and its decoder needs the noise; this asks for `epsilon = 0`, which the paper explicitly does not prove.
  hs-pcp-boone-compiler: that asks for matrix soundness on halting inputs with an infinite exact side on nonhalting inputs (coRE orientation); this asks for an exact finite-dimensional side on halting inputs and matrix soundness on nonhalting inputs (RE orientation), which is the orientation in which MIP* soundness is already available.
  bcs-to-lcs-exact-support-gap: that asks for an exact LCS sub-menu of one fixed tracial BCS with approximate soundness; this asks for the machine-indexed family with exact finite-dimensional completeness.
---

Construct a computable map `M -> L_M` from Turing machines to finite
binary linear constraint systems, with solution groups `Gamma_M` and
central involutions `J_M`, and a constant `delta > 0`, such that

```text
M halts          =>  Gamma_M has a finite-dimensional representation
                     with J_M = -I  (a perfect finite-dimensional LCS
                     strategy),                                        (PC1)
M does not halt  =>  omega_q(L_M) <= 1 - delta.                        (PC2)
```

By `re-oriented-lcs-compiler-gives-nonhyperlinear-group` this yields an
nonhyperlinear solution group `Gamma_M` for some nonhalting `M` (existence
only; the co-r.e. argument does not identify `M`).  Taller--Vidick prove `(PC2)` with
`delta = 1/72` and a version of `(PC1)` with value `1 - epsilon` only.

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
  create an exact finite-dimensional LCS solution.  Neither result supplies
  `(PC1)`, and Taller--Vidick v2 still explicitly identifies `epsilon=0` as
  the nonhyperlinear-group threshold.

**Note (2026-08-22 audit).**  `linear-encoding-lcs-admits-odd-subset-cheats`
is OPEN again: its global statement fails for sources with non-extendable
local assignments (`odd-subset-relaxation-needs-local-extendability`);
any "encodings cannot create LCS hardness" / "dies by the odd-subset
cheat" reasoning here holds only under local extendability of the source.
