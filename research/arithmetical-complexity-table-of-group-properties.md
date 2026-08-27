---
rg: 2
id: arithmetical-complexity-table-of-group-properties
kind: claim
title: Where the approximation, residual, amenability and rigidity properties of groups sit in the arithmetical hierarchy, by syntax
artifacts:
  - GroupApproximation/Computability/ArithmeticalLedgerEndpoint.lean
  - GroupApproximation/Computability/FreeSubgroupEnumeratedHardness.lean
  - GroupApproximation/Computability/TorsionFreeEnumeratedHardness.lean
  - GroupApproximation/Computability/AbelianEnumeratedPi02.lean
  - GroupApproximation/Computability/TrivialEnumeratedPi02.lean
  - GroupApproximation/Computability/ElementaryEnumeratedHardness.lean
  - GroupApproximation/Computability/IsoInvariantSwitchHardness.lean
  - GroupApproximation/Computability/AmenableEnumeratedHardness.lean
  - GroupApproximation/Computability/HyperlinearEnumeratedHardness.lean
  - GroupApproximation/Computability/RFEnumeratedHardness.lean
  - GroupApproximation/Computability/RFPresentationPi02.lean
  - GroupApproximation/Computability/HyperlinearUndecidabilityRoute.lean
  - GroupApproximation/Computability/ProfinitelyClosedIndexSet.lean
  - GroupApproximation/Computability/LEFEnumeratedPi02.lean
  - GroupApproximation/Computability/SoficEnumeratedPi02.lean
  - research/artifacts/arithmetical-complexity-note-2026-08-26.tex
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  second-level-rice-theorem-for-local-approximation-properties: that is one theorem; this is the ledger of all classifications, including the ones outside its scope (residual finiteness, amenability, property (T)), with every cell pointing at its proof and every open cell named.
  approximation-property-recognition-dichotomy: that is the conditional row for hyperlinearity; this places it beside the unconditional rows.
---

ESTABLISHED (as a ledger; each cell is a separate established claim, and the
cells marked OPEN are open claims).  Syntaxes: `fp` = finite presentations,
`rec2` = two-generator recursive presentations (`rec3`, `rec` = three
generators, finitely many generators), `V` = pairs of words in Higman's
universal finitely presented group, `enum` = countably generated
enumerated presentations.

```text
property           fp                          rec2 / rec                    enum
-------------------------------------------------------------------------------------
trivial            Sigma^0_1-complete (folk.)  Pi^0_2-complete (folk.)       Pi^0_2-complete
abelian            Pi^0_2 (folk.)              Pi^0_2-complete (folk.)       Pi^0_2-complete
torsion-free       Pi^0_2-complete [TF]        Pi^0_2-complete               Pi^0_2-complete
sofic              Pi^0_2 \ Pi^0_1, complete   Pi^0_2-complete               Pi^0_2-complete
                   OPEN [S]
operator-MF        Pi^0_2-complete [MF]        Pi^0_2-complete               Pi^0_2-complete
LEF                = RF_fp                     Pi^0_2-complete               Pi^0_2-complete
hyperlinear        trivial or Sigma^0_1-hard   trivial or Pi^0_2-complete    same
                   in Pi^0_2 \ Pi^0_1 [H]      [H]
weakly sofic,      as hyperlinear              as hyperlinear                same
linear sofic       (in Pi^0_2 \ Pi^0_1) [W]    (trivial or complete) [W]
finitely           --                          Sigma^0_2-hard, in Sigma^0_3  Sigma^0_2-hard, in Sigma^0_3
presentable                                    [FP]
amenable           Pi^0_2 \ Pi^0_1, complete   Pi^0_2-complete               Pi^0_2-complete
                   OPEN [A]
metabelian         Pi^0_2 (complete OPEN)      Pi^0_2-complete               Pi^0_2-complete
contains F_2       Sigma^0_2 (lower: Pi^0_1-h) Sigma^0_2-complete            Sigma^0_2-complete
residually finite  Pi^0_2 \ Pi^0_1, complete   Pi^0_3-complete               Pi^0_3-complete
                   OPEN [RF-Higman]
residually p       Pi^0_2 \ Pi^0_1 (as RF)     Pi^0_3-complete               Pi^0_3-complete
residually p for   --                          Sigma^0_4-complete            Sigma^0_4-complete
some prime p
property (T)       Sigma^0_1-complete          Sigma^0_1-complete (rec)      --
```

Legend.  `[S]` = [[sofic-safe-finite-presentation-compiler]];
`[MF]` = [[mf-recognition-finite-presentations-is-pi2-complete]];
`[H]` = [[approximation-property-recognition-dichotomy]], side (B) iff a
non-hyperlinear group exists;
`[A]` = [[amenability-of-finite-presentations-is-pi2-complete]];
`[W]` = [[weak-soficity-recognition-has-a-pi2-upper-bound]],
[[linear-soficity-recognition-has-a-pi2-upper-bound]] (side (B) iff some
group fails the property);
`[FP]` = [[finite-presentability-two-generator-recursive-is-sigma2-hard]];
`[TF]` = [[torsion-freeness-of-finite-presentations-is-pi2-complete]], via
[[finite-presentation-rice-criterion-via-the-fixed-positive-rope]];
`[RF-Higman]` = `Pi^0_2`-completeness of `RF_fp`, the residually finite
Higman problem.  Rows: sofic
[[sofic-recognition-two-generator-recursive-is-pi2-complete]],
[[sofic-recognition-finite-presentations-arithmetical-position]]; MF and LEF
[[mf-recognition-two-generator-recursive-is-pi2-complete]]; amenable,
metabelian, `F_2`
[[amenability-two-generator-recursive-is-pi2-complete]],
[[amenability-of-finite-presentations-arithmetical-position]]; residually
finite [[residual-finiteness-two-generator-recursive-is-pi3-complete]],
[[residual-finiteness-of-enumerated-presentations-is-pi3-complete]];
residually `p` [[residually-p-two-generator-recursive-is-pi3-complete]];
property (T) [[kazhdan-property-t-of-finite-presentations-is-sigma1-complete]];
the general engine [[second-level-rice-theorem-for-local-approximation-properties]].

Two structural readings.  (1) Every local approximation property lives at
level two on recursive presentations and is decided at level one only
trivially; the residual properties are one level higher on recursive
presentations, and collapse to level two only on finite presentations,
where the extra quantifier ("one finite quotient kills all relators") is
bounded.  (2) On finite presentations the exact level is known for (T)
(one, semidecidable) and unknown for every level-two candidate except MF,
each open cell being a form of a Higman-embedding question for that
property.

**Machine-checked cells.**  On enumerated presentation codes the sofic and LEF rows are kernel-checked as `Pi02Complete` (`SoficEnumeratedPi02.sofic_enum_pi02Complete`, `LEFEnumeratedPi02.lef_enum_pi02Complete`), the computability core of the residual-finiteness row as `ProfinitelyClosedIndexSet.pi03Complete_closedIndex`, and the hyperlinear finite-presentation equivalence as `HyperlinearUndecidabilityRoute.not_computablePred_iff_exists_nonhyperlinear_code`.

Also kernel-checked: `RFPresentationPi02.rf_fp_strict_position` (the residually finite finite-presentation cell), `RFEnumeratedHardness.rfCode_pi02Hard` (second-level lower bound on enumerated codes) and `HyperlinearEnumeratedHardness.hyperlinearCode_pi02Hard_of_exists`.

Amenability's second-level lower bound on enumerated codes is `AmenableEnumeratedHardness.amenableCode_pi02Hard`.

The `trivial` row's second-level lower bound and finiteness are `ElementaryEnumeratedHardness.trivialCode_pi02Hard` / `finiteCode_pi02Hard`; property (T)'s enumerated lower bound is `IsoInvariantSwitchHardness.kazhdanCode_pi02Hard` (isomorphism invariance suffices for the switch, heredity is not needed).

The `trivial` row on enumerated codes is fully kernel-checked: `TrivialEnumeratedPi02.trivial_enum_pi02Complete`.

Commutativity on enumerated codes is fully kernel-checked: `AbelianEnumeratedPi02.comm_enum_pi02Complete`.

Torsion-freeness is [[torsion-freeness-recognition-is-pi2-complete]] (hardness kernel-checked as `TorsionFreeEnumeratedHardness.torsionFreeCode_pi02Hard`), and the free-subgroup row's lower bound as `FreeSubgroupEnumeratedHardness.containsFreeSubgroupCode_sigma02Hard`.  The three levels are read as a hierarchy theorem in [[natural-group-properties-realize-the-first-three-levels]].

**The finite-presentation cells have one common gate.**  By [[finite-presentation-rice-criterion-via-the-fixed-positive-rope]], a hereditary property is `Pi^0_2`-hard on finite presentations as soon as the MF compiler's positive rope has it.  The rope is MF and torsion-free, is not amenable and is not residually finite, and its soficity and hyperlinearity are open: this is exactly the pattern of closed and open cells above.

**One endpoint.**  `Computability/ArithmeticalLedgerEndpoint.arithmetical_ledger` is this ledger's machine-checked cells conjoined into a single closed proposition.

The fourth level is realized too: [[residually-p-for-some-prime-is-sigma4-complete]].

## Prior and adjacent work (2026-08-26 literature sweep)

**Must cite, and subsumes one of our theorems.**  Iva Bilanovic, Jennifer
Chubb, Sam Roven, "Detecting properties from descriptions of groups",
Archive for Mathematical Logic 59 (2019/2020) 293-312, DOI
10.1007/s00153-019-00690-x (arXiv:1903.05143).  Their Theorem 3.1: every
Markov property is `Pi^0_2`-hard on recursively presented (countably
generated) groups, proved by the same kill-one-copy construction as our
event ray (`G_+ * G_- * G_- * ...`, one `G_-` killed per enumeration
event).  Since a hereditary property with a counterexample is Markov, the
countably generated clause of
[[second-level-rice-theorem-for-local-approximation-properties]] (and the
kernel-checked `enumeratedCodeProperty_pi02Hard`) IS their theorem; it must
be attributed to them, not claimed.  Also theirs: `Pi^0_2`-completeness of
trivial/abelian/torsion-free/torsion/divisible/orderable on r.p. groups
(their Cor. 3.2, our "(folk.)" cells), and `Sigma^0_3`-completeness of
finiteness, decidable word problem, cyclic, nilpotent, solvable and finite
presentability on r.p. groups (so the countably generated
finite-presentability and word-problem cells are theirs; only the
two-generator refinements remain ours or open).  What is NOT in their
paper and remains this ledger's content: every finite-presentation cell
([TF] is Lempp, which they cite as the one known fp example; [MF] is ours
and is the second such theorem), the `Pi^0_2` upper bounds for sofic,
hyperlinear, MF and LEF recognition (non-obvious certificate normal forms
with word-problem-oracle elimination), the level-three `Pi^0_3` residual
finiteness cells, the two-generator and fixed-ambient `V` syntaxes, and
property (T).  The hyperlinear dichotomy's recursive-presentation half is a
corollary of their theorem plus marked closedness; only its upper bound
and finite-presentation side are ours.

The two Tech Insider pieces of 2026-08-17/18 on the Manifold market "Will
the existence of a non-MF group be proved this month" confirm the public
state of the art consumed by this ledger: as of 2026-08-18 no public
paper, preprint, or certificate claims a non-MF group; the market movement
is momentum from the 2026-08-01 OpenAI Astra release (first non-sofic
group + Connes-rigidity disproof, Lean-certified), which is exactly the
[[binary-leavitt-unit-group-hyperlinear]] seed family this graph already
consumes.  Kivanc Ersoy, arXiv:2604.19174, develops the structure theory
of minimal non-sofic groups conditionally on existence; those results read
unconditionally against the Astra witness.
