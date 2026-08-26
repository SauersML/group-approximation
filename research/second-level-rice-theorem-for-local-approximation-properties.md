---
rg: 2
id: second-level-rice-theorem-for-local-approximation-properties
kind: claim
title: Every nontrivial local approximation property is Pi-zero-two hard on two-generator recursive presentations and undecidable on finite presentations
artifacts:
  - GroupApproximation/Computability/SoficRecognitionSecondLevel.lean
  - GroupApproximation/Computability/HereditaryRecognitionPhaseDiagram.lean
  - GroupApproximation/Computability/HereditaryPropertySwitchCompleteness.lean
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
  - GroupApproximation/Computability/ParametricFinInfSwitch.lean
  - GroupApproximation/Computability/AdianRabinGeneral.lean
  - GroupApproximation/Computability/SoficMarkov.lean
distinct_from:
  arbitrary-forbidden-seed-hereditary-property-switch: that is the countably generated switch and needs a finitely presented forbidden seed handed to it; this supplies the seed from any finitely generated counterexample by the marked-group cover, adds the two-generator bridge and the fixed ambient, and draws the finite-presentation Markov consequences.
  mf-recognition-two-generator-recursive-is-pi2-complete: that is the MF and LEF instance with the literal seed; this is the property-free theorem whose only external input is one finitely generated counterexample, and it covers soficity, hyperlinearity, weak and linear soficity uniformly.
  operator-mf-is-a-markov-property: that verifies the three Markov clauses for one property; this proves that every nontrivial local approximation property containing the residually finite groups is Markov, and continues to the second level.
  mf-recognition-undecidable: that is the first-level MF statement; this is the general theorem for all local approximation properties at both levels.
---

ESTABLISHED.  Let `P = P_M` be a local approximation property in the sense of
[[local-approximation-properties-are-marked-closed]] and assume

```text
(H1)  every residually finite group has P     (it suffices that B2(1) has P),
(H2)  some finitely generated group fails P.
```

Then:

**(a) Finite presentations.**  Some finitely presented group fails `P`; `P`
is a Markov property of finitely presented groups; the set `P_fp` of finite
presentation codes whose group has `P` is `Sigma^0_1`-hard and its
complement is `Pi^0_1`-hard.  Hence `NON-P_fp` is not recursively
enumerable, `P_fp` is not co-recursively-enumerable, and neither is
decidable.

**(b) Two-generator recursive presentations.**  There is one computable map
`e |-> Q_e` into two-generator recursive presentations with

```text
e in INF  ==>  Q_e ~= B2(1), residually finite, so Q_e has P,
e in FIN  ==>  Q_e contains a finitely presented group failing P, so Q_e fails P.
```

Hence `P_rec2` is `Pi^0_2`-hard and `NON-P_rec2` is `Sigma^0_2`-hard under
computable many-one reductions.  Two generators is optimal: one-generator
groups are cyclic and have `P` by (H1).

**(c) One fixed ambient group.**  For Higman's universal finitely presented
group `V`, the set of pairs of words `(u_1, u_2)` with `<u_1, u_2> <= V`
having `P` is `Pi^0_2`-hard.

**(d) Completeness.**  If in addition `P_rec` is `Pi^0_2` (true for sofic
[[sofic-recognition-has-a-pi2-upper-bound]], LEF
[[lef-recognition-has-a-pi2-upper-bound]], operator-MF
[[mf-recognition-has-a-pi2-upper-bound]], and hyperlinear
[[nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound]] with a
relator prefix in the certificate), then `P_rec2` and the fixed-ambient
problem are `Pi^0_2`-complete, their complements `Sigma^0_2`-complete, and

```text
P_fp in Pi^0_2 \ Pi^0_1,        NON-P_fp in Sigma^0_2 \ Sigma^0_1.
```

**What the theorem does not say.**  It does not place `P_fp` at
`Pi^0_2`-completeness; that requires a `P`-safe finite-presentation
compiler, which for MF is [[mf-safe-finite-presentation-compiler]] and for
soficity is the open [[sofic-safe-finite-presentation-compiler]].

**Reading.**  This is Rice's theorem one level up: for the properties by
which groups are approximated by finite or finite-dimensional objects, the
*only* obstacle to `Pi^0_2`-hardness is the existence of a single
counterexample, and that counterexample need not be finitely presented, nor
even recursively presented.  Instances are drawn in
[[sofic-recognition-two-generator-recursive-is-pi2-complete]],
[[sofic-recognition-finite-presentations-arithmetical-position]] and
[[approximation-property-recognition-dichotomy]].

**Machine-checked phase theorem.**
`Computability/HereditaryRecognitionPhaseDiagram` isolates exactly the abstract
input used here: subgroup heredity, truth on the trivial group, and a finite
counterexample cover.  It proves that existence of an abstract counterexample
is equivalent both to `Pi02Hard P_rec` and to `Sigma02Hard NON-P_rec`, packages
the universal-computable/hard-counterexample alternatives as an unconditional
dichotomy, and upgrades both equivalences to completeness from a `Pi02` upper
bound.  `Computability/HyperlinearRecognitionSecondLevel` is a checked client
of this generic interface, with its finite cover supplied by the hyperlinear
table obstruction theorem.
