---
rg: 2
id: approximation-property-recognition-dichotomy
kind: claim
title: Recognizing hyperlinearity is either trivial or Pi-zero-two complete, and a non-hyperlinear group exists iff it is undecidable
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
  - GroupApproximation/Covers/HyperlinearTableCover.lean
  - GroupApproximation/Computability/HyperlinearMarkov.lean
  - GroupApproximation/Computability/HereditaryRecognitionPhaseDiagram.lean
  - GroupApproximation/Computability/HyperlinearRecognitionSecondLevel.lean
distinct_from:
  nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound: that is the upper bound alone and says so; this adds the matching lower bound conditional on exactly one thing, the existence of a non-hyperlinear group, and shows nothing in between can happen.
  non-hyperlinear-group: that asks for a group; this is a theorem about decision problems whose two sides are the two possible answers to that question, and it is established whichever answer is true.
  second-level-rice-theorem-for-local-approximation-properties: that is the general engine; this is its consequence for the properties whose universality is open, stated as a dichotomy so that a decidability proof and a counterexample are seen to be the same discovery.
---

ESTABLISHED (as a dichotomy; which side holds is exactly the open question).
Let `HYP_rec2`, `HYP_fp` and `HYP_V` be hyperlinearity on two-generator
recursive presentations, on finite presentation codes, and on pairs of words
in Higman's universal group `V`.  Exactly one of the following holds.

```text
(A)  Every group is hyperlinear.  Then HYP_rec2, HYP_fp, HYP_V are the
     full sets, hence decidable.

(B)  Some group is not hyperlinear.  Then HYP_rec2 and HYP_V are
     Pi^0_2-complete, their complements Sigma^0_2-complete, HYP_fp is
     Sigma^0_1-hard and in Pi^0_2 \ Pi^0_1, and NONHYP_fp is Pi^0_1-hard
     and in Sigma^0_2 \ Sigma^0_1.                                    (D1)
```

In particular the following are equivalent:

```text
(i)   a non-hyperlinear group exists;
(ii)  a finitely presented non-hyperlinear group exists;
(iii) HYP_fp is undecidable;
(iv)  HYP_rec2 is undecidable;
(v)   HYP_rec2 is Pi^0_2-complete;
(vi)  NONHYP_fp is not recursively enumerable;
(vii) HYP_rec is Pi^0_2-hard on enumerated presentation codes;
(viii) NONHYP_rec is Sigma^0_2-hard on those same codes.               (D2)
```

The equivalence `(i) <=> (ii)` is machine-checked as
`exists_not_isHyperlinear_iff_exists_finitelyPresented`.  The equivalence
between `(i)` and undecidability of `HYP_fp` is machine-checked as
`exists_not_isHyperlinear_iff_codeProperty_not_computable`; its forward
direction constructs the Adian--Rabin data from the finite table cover, and
`exists_not_isHyperlinear_iff_nonhyperlinearCodeProperty_not_re` checks the
full equivalence with the stronger non-r.e. conclusion for the negative side.
The complementary easy side is checked by
`no_counterexample_iff_hyperlinearCodeProperty_computable` and
`no_counterexample_iff_nonhyperlinearCodeProperty_re`.  Finally,
`exists_not_isHyperlinear_iff_nonempty_markovData` identifies the exact phase
transition: hyperlinearity admits Adian--Rabin Markov data precisely when a
counterexample exists.  The still stronger audited endpoint
`exists_not_isHyperlinear_iff_nonempty_adianRabinReduction` says the same for
an explicit computable many-one reduction from the uniform word problem.  The
three parallel `exists_nonhyperlinear_code_iff_*` endpoints sharpen this to the
actual finite-presentation coding: existence of a forbidden code is equivalent
to undecidability, to non-r.e.-ness of the negative code set, and to inhabitation
of the explicit reduction type.  Finally,
`Computability/HyperlinearRecognitionSecondLevel` machine-checks `(i) <=>
(vii) <=> (viii)`.  Its forward maps are the arbitrary-forbidden-seed event-ray
compiler; its reverse maps prove directly that constant-true and constant-false
predicates cannot be hard at the corresponding second level.  The unconditional
audited theorem `hyperlinear_recognition_phase_dichotomy` packages both regimes:
either all groups are hyperlinear and the positive/negative enumerated-code
predicates are computable/recursively enumerable, or a counterexample exists
and those predicates are respectively `Pi02Hard`/`Sigma02Hard`; a companion
theorem proves the branches disjoint.  The two `*_Complete` equivalences also
show that any effective `Pi02` upper bound upgrades exactly the counterexample
branch, and only that branch, to matching completeness.
These are now instances of the reusable audited theorem in
`Computability/HereditaryRecognitionPhaseDiagram`, rather than duplicated
hyperlinearity-specific recursion-theoretic arguments.

The same dichotomy holds verbatim for **weak soficity** (with the
`Pi^0_2` membership supplied by
[[weak-soficity-recognition-has-a-pi2-upper-bound]], so the row is a
completeness dichotomy) and for **linear soficity** over any fixed field,
and for every local approximation property that contains the residually
finite groups, with "`Pi^0_2`-complete" read as "`Pi^0_2`-hard" where the
corresponding upper bound is not yet recorded.  For
soficity and operator-MF side (B) is known to hold.

**Why this matters for the goal.**  (D2) turns [[non-hyperlinear-group]] into
a statement about a decision problem.  This is the same shape as the proof
that Connes' embedding problem has a negative answer: MIP* = RE exhibits no
algebra, it shows that a value problem is undecidable and lets the
arithmetical hierarchy produce the counterexample.  A reduction from the
halting problem (or from `INF`) to `HYP_fp` would prove (iii), hence (i),
without constructing a group; the route
[[non-hyperlinear-from-hyperlinear-recognition-undecidable]] records this,
and [[hyperlinear-recognition-undecidable]] is the open claim that any such
reduction would establish.  Conversely every candidate non-hyperlinear group
is, by (D1), simultaneously a proof that hyperlinearity is
`Pi^0_2`-complete on recursive presentations.
