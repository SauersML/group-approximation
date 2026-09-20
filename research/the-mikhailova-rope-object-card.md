---
rg: 2
id: the-mikhailova-rope-object-card
kind: claim
title: The Mikhailova rope family and its sufficient tests for finite-presentation recognition
artifacts:
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  mf-safe-finite-presentation-compiler: that is the fixed-seed compiler theorem; this inventories its parameterized positive ropes and sufficient tests for recognition, without asserting seed-independent isomorphism types.
  finite-presentation-rice-criterion-via-the-fixed-positive-rope: that is the criterion; this is its input, made explicit so that a reader can attack the right object.
---

Inventory. Fix a finite seed code d and an input e with infinite domain.
Write R=R_e(d) for the actual output of
[[mf-compiler-is-uniform-in-finite-seeds]], without identifying outputs
for different seeds or indices. Explicitly, with
`K = F x F(X) x F(X) x F x P` a finite direct
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

**Open sufficient conditions for cells of the ledger.**

```text
all R_e(d) sofic, every d and e in INF       => SOFIC_fp Pi^0_2-complete
all R_e(d) hyperlinear, every d and e in INF => the hyperlinear finite-presentation cell
                  [[hyperlinear-fp-recognition-complete-iff-nonhyperlinear-group]]
```

These are not converses: another compiler could establish completeness
while this family's positive branch fails. The family quantifier over
every seed d and e in INF is essential; the notation R does not assert that all
Higman hosts or all resulting ropes are isomorphic. The 2026-09-20
Liu-based MF/nonhyperlinear separation removes the universal MF shortcut
without deciding either property of these particular ropes.

**What is ruled out for the sofic question.** An exact finite quotient
action of K with a stable letter exactly centralizing the entire image
of L kills the closure-point pinches when L is nonseparable; this is
the actual argument in
[[centralizing-hnn-sofic-via-regular-edge-centralizer]]. It does not
exclude approximate stable-letter commutation with the edge generators,
even if the finite K action is exact: word lengths expressing a closure
point in the finite edge image need not stay bounded. Approximate base
models are another available source of flexibility.

**Why an object card.** The family supplies concrete sufficient tests
for several cells of [[arithmetical-complexity-table-of-group-properties]].
Neither equivalence of those recognition problems nor one common
isomorphism type of the positive outputs is claimed.
