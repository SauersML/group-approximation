---
rg: 2
id: the-mikhailova-rope-object-card
kind: claim
title: The Mikhailova rope, one explicit finitely presented group that carries every open finite-presentation cell
artifacts:
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  mf-safe-finite-presentation-compiler: that is the compiler and the theorem that its positive branch is MF; this is the group itself, listed with everything now known and unknown about it, because the open cells of the ledger have all been reduced to properties of it.
  finite-presentation-rice-criterion-via-the-fixed-positive-rope: that is the criterion; this is its input, made explicit so that a reader can attack the right object.
---

ESTABLISHED (as an inventory).  Write `R` for the positive-branch output
of the MF-safe finite-presentation compiler on an input with infinite
domain --- explicitly, with `K = F x F(X) x F(X) x F x P` a finite direct
product of finitely generated free groups, `M` a Mikhailova subgroup of
`F(X) x F(X)` for a finitely presented group with unsolvable word problem,
`L <= K` the corresponding edge subgroup, `Q = B3(1) = (F_oo x F_oo) x| Z`
and `tau` the graph map of the compiler,

```text
Gamma = < K, v | [v, L] = 1 >,
R     = < Gamma x Q, u | u (s, 1) u^-1 = (s, tau(s)),  s in S >.        (MR1)
```

**Known.**

```text
finitely presented                      yes (compiler)
operator-MF                             yes (compiler)
torsion-free                            yes  [[mf-compiler-positive-branch-is-torsion-free]]
residually finite                       NO   (the edge is non-separable:
                                              [[centralizing-hnn-is-residually-finite-iff-edge-is-separable]])
LEF                                     NO   [[mikhailova-positive-rope-is-not-lef]]
contains a free subgroup of rank two    yes (K does)
amenable                                NO
```

**Open, and each equivalent to a cell of the ledger.**

```text
sofic        <=>  SOFIC_fp is Pi^0_2-complete      [[sofic-safe-finite-presentation-compiler]]
hyperlinear  <=>  the hyperlinear finite-presentation cell
                  [[hyperlinear-fp-recognition-complete-iff-nonhyperlinear-group]]
```

**What is already ruled out for the sofic question.**  Any finite model
whose restriction to `K` is a homomorphism onto a finite quotient fails,
because the edge is finitely generated and non-separable
([[centralizing-hnn-sofic-via-regular-edge-centralizer]]); the surviving
freedom is that local models need only be multiplicative on a ball, and
that a free edge action supplies an exact stable letter.

**Why an object card.**  Three open cells of
[[arithmetical-complexity-table-of-group-properties]] are the same
question about this one group; anyone attacking them should attack `R`
directly rather than rebuild a compiler.
